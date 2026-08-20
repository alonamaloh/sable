//! Closed, kernel-checked certificates for call argument evaluation order.
//!
//! This is intentionally a post-check extractor, not another admission
//! helper. It walks the typed expression AST directly, consumes exact records
//! from [`CheckedOwnershipPlan`], and emits a closed Lean schedule for each
//! user or compiler-sealed boundary in every checked non-extern body. It does
//! not call the checker's pending-loan or mutation-collection routines and it
//! does not use `BodyPlan` as an expression CFG.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::ast::{Expr, ExprKind, IntTy, Mutability, Param, Program, SelfKind, SlotOp, Stmt, Ty};
use crate::ownership::{
    CheckedOwnershipPlan, CheckedSealedOperation, CheckedSealedTarget, CheckedSlotTransition,
    CheckedSlotTransitionKind, EffectSiteKey, ValueTransfer, ValueTransferKey, ValueTransferKind,
    ValueTransferSink,
};
use crate::place::{BorrowedPlace, Place};
use crate::span::Span;
use crate::transition::{
    CallArgumentEffect, CallEffect, CallOwner, CallSiteKey, CallTarget, CheckedCallTransition,
};
use std::collections::HashSet;

pub(crate) const MAX_ARGUMENTS: usize = 64;
pub(crate) const MAX_NESTED_EFFECTS: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DirectEffect {
    Inert,
    Loan { place: Place, unique: bool },
    Move { place: Place },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NestedEffect {
    Write(Place),
    Move(Place),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RankedArgument {
    pub(crate) rank: usize,
    pub(crate) nested: Vec<NestedEffect>,
    pub(crate) direct: DirectEffect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArgumentSchedule {
    pub(crate) receiver: DirectEffect,
    pub(crate) arguments: Vec<RankedArgument>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Boundary {
    Call(CallTarget),
    Sealed(CheckedSealedTarget),
    Slot(&'static str),
}

impl Boundary {
    fn component(&self) -> String {
        match self {
            Self::Call(target) => format!("call.{}", target.certificate_component()),
            Self::Sealed(target) => format!("sealed.{}", target.render()),
            Self::Slot(operation) => format!("slot.{operation}"),
        }
    }

    fn render(&self) -> String {
        match self {
            Self::Call(target) => target.render(),
            Self::Sealed(target) => format!("sealed operation `{}`", target.render()),
            Self::Slot(operation) => format!("sealed owner-slot operation `{operation}`"),
        }
    }
}

/// One non-skippable, closed theorem in the generated artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArgumentScheduleCertificate {
    pub(crate) name: String,
    pub(crate) thm_name: String,
    pub(crate) span: Span,
    boundary: Boundary,
    pub(crate) schedule: ArgumentSchedule,
}

impl ArgumentScheduleCertificate {
    pub(crate) fn description(&self) -> &'static str {
        "argument-schedule"
    }

    pub(crate) fn boundary(&self) -> String {
        self.boundary.render()
    }

    pub(crate) fn lean_goal(&self) -> String {
        format!(
            "Sable.ArgumentSchedule.safe ({}) = true",
            lean_schedule(&self.schedule)
        )
    }

    pub(crate) fn lean_proof(&self) -> &'static str {
        "by decide"
    }

    pub(crate) fn rejection_diagnostic_name(&self) -> &'static str {
        "internal.argument_schedule_certificate_rejected"
    }

    pub(crate) fn rejection_label(&self) -> String {
        format!(
            "the recorded left-to-right effects of {} are not alias-safe",
            self.boundary.render()
        )
    }
}

/// Extract every checked non-extern callable's schedules from the typed AST
/// and exact checker ownership records. Dynamic `test_` bodies and
/// proof-reusing instances still receive these closed certificates.
pub(crate) fn extract(
    program: &Program,
    ownership: &CheckedOwnershipPlan,
) -> Result<Vec<ArgumentScheduleCertificate>, String> {
    let mut extractor = Extractor {
        program,
        ownership,
        certificates: Vec::new(),
        theorem_names: HashSet::new(),
        visited_calls: HashSet::new(),
        visited_sealed: HashSet::new(),
        visited_slots: HashSet::new(),
        visited_option_takes: HashSet::new(),
        visited_expression_transfers: HashSet::new(),
    };

    for function in &program.fns {
        if function.extern_info.is_some() {
            continue;
        }
        extractor.extract_body(
            CallOwner::Function(function.name.clone()),
            function.span,
            &function.body,
        )?;
    }
    for function in &program.fn_templates {
        extractor.extract_body(
            CallOwner::Function(function.name.clone()),
            function.span,
            &function.body,
        )?;
    }
    for class in &program.class_templates {
        extractor.extract_class(class)?;
    }
    for class in &program.classes {
        extractor.extract_class(class)?;
    }
    extractor.finish_global()?;
    Ok(extractor.certificates)
}

struct Extractor<'a> {
    program: &'a Program,
    ownership: &'a CheckedOwnershipPlan,
    certificates: Vec<ArgumentScheduleCertificate>,
    theorem_names: HashSet<String>,
    visited_calls: HashSet<CallSiteKey>,
    visited_sealed: HashSet<EffectSiteKey>,
    visited_slots: HashSet<EffectSiteKey>,
    visited_option_takes: HashSet<EffectSiteKey>,
    visited_expression_transfers: HashSet<ValueTransferKey>,
}

impl Extractor<'_> {
    fn extract_class(&mut self, class: &crate::ast::ClassDecl) -> Result<(), String> {
        for init in &class.inits {
            self.extract_body(
                CallOwner::Constructor {
                    class: class.name.clone(),
                    init: init.name.clone(),
                },
                init.span,
                &init.body,
            )?;
        }
        for method in &class.methods {
            self.extract_body(
                CallOwner::Method {
                    class: class.name.clone(),
                    method: method.f.name.clone(),
                },
                method.f.span,
                &method.f.body,
            )?;
        }
        if let Some(body) = class.deinit.as_ref().filter(|body| !body.is_empty()) {
            self.extract_body(
                CallOwner::Deinitializer {
                    class: class.name.clone(),
                },
                class.span,
                body,
            )?;
        }
        Ok(())
    }

    fn extract_body(
        &mut self,
        owner: CallOwner,
        declaration_span: Span,
        body: &[Stmt],
    ) -> Result<(), String> {
        for statement in body {
            self.visit_statement(&owner, declaration_span, statement)?;
        }
        self.finish_owner(&owner)
    }

    fn visit_statement(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        statement: &Stmt,
    ) -> Result<(), String> {
        match statement {
            Stmt::Decl { init, .. } => {
                if let Some(expression) = init {
                    self.visit_expression(owner, declaration_span, expression)?;
                }
            }
            Stmt::Assign { value, .. }
            | Stmt::VarDecl { init: value, .. }
            | Stmt::FieldAssign { value, .. }
            | Stmt::ExprStmt(value) => {
                self.visit_expression(owner, declaration_span, value)?;
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.visit_expression(owner, declaration_span, cond)?;
                for nested in then_block {
                    self.visit_statement(owner, declaration_span, nested)?;
                }
                if let Some(block) = else_block {
                    for nested in block {
                        self.visit_statement(owner, declaration_span, nested)?;
                    }
                }
            }
            Stmt::Return { value, .. } => {
                if let Some(expression) = value {
                    self.visit_expression(owner, declaration_span, expression)?;
                }
            }
            Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                self.visit_expression(owner, declaration_span, index)?;
                self.visit_expression(owner, declaration_span, value)?;
            }
            Stmt::While { cond, body, .. } => {
                self.visit_expression(owner, declaration_span, cond)?;
                for nested in body {
                    self.visit_statement(owner, declaration_span, nested)?;
                }
            }
            Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => {
                for nested in body {
                    self.visit_statement(owner, declaration_span, nested)?;
                }
            }
            Stmt::StaticAlloc { size, .. } | Stmt::SystemAlloc { size, .. } => {
                self.visit_expression(owner, declaration_span, size)?;
            }
            Stmt::SystemDealloc {
                ptr, res, release, ..
            } => {
                self.visit_expression(owner, declaration_span, ptr)?;
                self.visit_expression(owner, declaration_span, res)?;
                self.visit_expression(owner, declaration_span, release)?;
            }
            Stmt::Assert(_) => {}
        }
        Ok(())
    }

    /// Return the completed writes and moves visible to an enclosing
    /// argument. Direct loans never escape their own callee boundary: a
    /// unique one returns as a completed write and a shared one is a transient
    /// read.
    fn visit_expression(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        expression: &Expr,
    ) -> Result<Vec<NestedEffect>, String> {
        match &expression.kind {
            ExprKind::Call { callee, args, .. } => self.visit_call(
                owner,
                declaration_span,
                expression,
                CallTarget::Function(callee.clone()),
                args,
                None,
            ),
            ExprKind::CtorCall {
                class, init, args, ..
            } => self.visit_call(
                owner,
                declaration_span,
                expression,
                CallTarget::Constructor {
                    class: class.clone(),
                    init: init.clone(),
                },
                args,
                None,
            ),
            ExprKind::MethodCall {
                recv,
                recv_span,
                method,
                args,
                ..
            } => {
                let target = self.resolve_method_target(owner, expression, method)?;
                self.visit_call(
                    owner,
                    declaration_span,
                    expression,
                    target,
                    args,
                    Some((recv.as_str(), *recv_span)),
                )
            }
            ExprKind::RawOp { op, args, .. } => self.visit_sealed(
                owner,
                declaration_span,
                expression,
                CheckedSealedTarget::Raw(*op),
                args,
            ),
            ExprKind::ResOp { op, args, .. } => self.visit_sealed(
                owner,
                declaration_span,
                expression,
                CheckedSealedTarget::Resource(*op),
                args,
            ),
            ExprKind::DeviceOp { op, args, .. } => self.visit_sealed(
                owner,
                declaration_span,
                expression,
                CheckedSealedTarget::Device(*op),
                args,
            ),
            ExprKind::SlotOp { op, op_span, args } => self.visit_slot(
                owner,
                declaration_span,
                expression,
                op.clone(),
                *op_span,
                args,
            ),
            ExprKind::OptTake {
                option,
                option_span,
            } => {
                let key = EffectSiteKey {
                    owner: owner.clone(),
                    span: expression.span,
                };
                let take = self.ownership.option_take(&key).ok_or_else(|| {
                    format!(
                        "internal.argument_schedule.option_take_missing: no checked option extraction at {}..{} inside {}",
                        expression.span.start,
                        expression.span.end,
                        owner.render()
                    )
                })?;
                if take.key != key
                    || take.source != Place::local(option)
                    || take.source_span != *option_span
                    || expression.ty.as_ref() != Some(&take.payload)
                {
                    return Err(format!(
                        "internal.argument_schedule.option_take_mismatch: checked option extraction at {}..{} disagrees with the typed AST inside {}",
                        expression.span.start,
                        expression.span.end,
                        owner.render()
                    ));
                }
                if !self.visited_option_takes.insert(key) {
                    return Err(duplicate_visit("option extraction", expression.span, owner));
                }
                Ok(vec![NestedEffect::Write(take.source.clone())])
            }
            ExprKind::Unary { operand, .. }
            | ExprKind::Widen { arg: operand, .. }
            | ExprKind::Narrow { arg: operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand } => {
                self.visit_expression(owner, declaration_span, operand)
            }
            ExprKind::SomeE(inner) => {
                let mut effects = self.visit_expression(owner, declaration_span, inner)?;
                if expression.ty.as_ref().is_some_and(Ty::is_affine_option) {
                    let key = ValueTransferKey {
                        owner: owner.clone(),
                        span: inner.span,
                        sink: ValueTransferSink::OptionPayload,
                    };
                    let transfer = self.ownership.value_transfer(&key).ok_or_else(|| {
                        format!(
                            "internal.argument_schedule.option_payload_missing: no checked option-payload transfer at {}..{} inside {}",
                            inner.span.start,
                            inner.span.end,
                            owner.render()
                        )
                    })?;
                    let expected_ty = inner.ty.as_ref().ok_or_else(|| {
                        schedule_mismatch(
                            "option payload",
                            inner.span,
                            owner,
                            "typed inner expression has no type",
                        )
                    })?;
                    validate_value_transfer(transfer, inner, expected_ty).map_err(|detail| {
                        schedule_mismatch("option payload", inner.span, owner, &detail)
                    })?;
                    if let DirectEffect::Move { place } = direct_value(transfer) {
                        effects.push(NestedEffect::Move(place));
                    }
                    if !self.visited_expression_transfers.insert(key) {
                        return Err(duplicate_visit(
                            "option-payload transfer",
                            inner.span,
                            owner,
                        ));
                    }
                }
                Ok(effects)
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                let mut effects = self.visit_expression(owner, declaration_span, lhs)?;
                effects.extend(self.visit_expression(owner, declaration_span, rhs)?);
                Ok(effects)
            }
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => {
                self.visit_expression(owner, declaration_span, index)
            }
            ExprKind::AllocArray { len, init, .. } => {
                let mut effects = self.visit_expression(owner, declaration_span, len)?;
                effects.extend(self.visit_expression(owner, declaration_span, init)?);
                Ok(effects)
            }
            ExprKind::ArrayLit(elements)
            | ExprKind::TraitCall { args: elements, .. }
            | ExprKind::RecordLit { args: elements, .. } => {
                self.visit_expression_list(owner, declaration_span, elements)
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::NoneE
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::Borrow { .. } => Ok(Vec::new()),
        }
    }

    fn visit_expression_list(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        expressions: &[Expr],
    ) -> Result<Vec<NestedEffect>, String> {
        let mut effects = Vec::new();
        for expression in expressions {
            effects.extend(self.visit_expression(owner, declaration_span, expression)?);
        }
        Ok(effects)
    }

    fn visit_call(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        expression: &Expr,
        target: CallTarget,
        arguments: &[Expr],
        receiver: Option<(&str, Span)>,
    ) -> Result<Vec<NestedEffect>, String> {
        let key = CallSiteKey {
            owner: owner.clone(),
            span: expression.span,
            target: target.clone(),
        };
        let checked = self.ownership.calls.get(&key).cloned().ok_or_else(|| {
            format!(
                "internal.argument_schedule.call_missing: no checked record for {} at {}..{} inside {}",
                target.render(),
                expression.span.start,
                expression.span.end,
                owner.render()
            )
        })?;
        if checked.key != key {
            return Err(schedule_mismatch(
                "call",
                expression.span,
                owner,
                "embedded record key differs from its exact table identity",
            ));
        }
        self.validate_call(&checked, &target, expression, arguments, receiver)?;
        if !self.visited_calls.insert(key.clone()) {
            return Err(duplicate_visit("call", expression.span, owner));
        }

        let mut nested = Vec::with_capacity(arguments.len());
        for argument in arguments {
            nested.push(self.visit_expression(owner, declaration_span, argument)?);
        }
        let schedule = ArgumentSchedule {
            receiver: checked
                .receiver
                .as_ref()
                .map_or(DirectEffect::Inert, |receiver| {
                    direct_loan(&receiver.transition)
                }),
            arguments: checked
                .arguments
                .iter()
                .zip(nested.iter())
                .enumerate()
                .map(|(index, (argument, nested))| RankedArgument {
                    rank: index + 1,
                    nested: nested.clone(),
                    direct: direct_effect(&argument.effect),
                })
                .collect(),
        };
        self.push_certificate(
            owner,
            declaration_span,
            expression.span,
            Boundary::Call(target),
            schedule.clone(),
        )?;
        Ok(completed_boundary_effects(&schedule))
    }

    fn visit_sealed(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        expression: &Expr,
        target: CheckedSealedTarget,
        arguments: &[Expr],
    ) -> Result<Vec<NestedEffect>, String> {
        let key = EffectSiteKey {
            owner: owner.clone(),
            span: expression.span,
        };
        let checked = self
            .ownership
            .sealed_operation(&key)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "internal.argument_schedule.sealed_missing: no checked record for `{}` at {}..{} inside {}",
                    target.render(),
                    expression.span.start,
                    expression.span.end,
                    owner.render()
                )
            })?;
        if checked.key != key {
            return Err(schedule_mismatch(
                "sealed operation",
                expression.span,
                owner,
                "embedded record key differs from its exact table identity",
            ));
        }
        self.validate_sealed(&checked, target, expression, arguments)?;
        if !self.visited_sealed.insert(key.clone()) {
            return Err(duplicate_visit("sealed operation", expression.span, owner));
        }
        let mut nested = Vec::with_capacity(arguments.len());
        for argument in arguments {
            nested.push(self.visit_expression(owner, declaration_span, argument)?);
        }
        let schedule = ArgumentSchedule {
            receiver: DirectEffect::Inert,
            arguments: checked
                .arguments
                .iter()
                .zip(nested.iter())
                .enumerate()
                .map(|(index, (argument, nested))| RankedArgument {
                    rank: index + 1,
                    nested: nested.clone(),
                    direct: direct_effect(&argument.effect),
                })
                .collect(),
        };
        self.push_certificate(
            owner,
            declaration_span,
            expression.span,
            Boundary::Sealed(target),
            schedule.clone(),
        )?;
        Ok(completed_boundary_effects(&schedule))
    }

    fn visit_slot(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        expression: &Expr,
        operation: SlotOp,
        op_span: Span,
        arguments: &[Expr],
    ) -> Result<Vec<NestedEffect>, String> {
        let key = EffectSiteKey {
            owner: owner.clone(),
            span: expression.span,
        };
        let checked = self
            .ownership
            .slot_transition(&key)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "internal.argument_schedule.slot_missing: no checked owner-slot record at {}..{} inside {}",
                    expression.span.start,
                    expression.span.end,
                    owner.render()
                )
            })?;
        if checked.key != key {
            return Err(schedule_mismatch(
                "owner-slot operation",
                expression.span,
                owner,
                "embedded record key differs from its exact table identity",
            ));
        }
        let direct = self.validate_slot(&checked, &operation, op_span, expression, arguments)?;
        if !self.visited_slots.insert(key.clone()) {
            return Err(duplicate_visit(
                "owner-slot operation",
                expression.span,
                owner,
            ));
        }
        if let CheckedSlotTransitionKind::Put { value_transfer, .. } = &checked.kind {
            if !self
                .visited_expression_transfers
                .insert(value_transfer.clone())
            {
                return Err(duplicate_visit(
                    "slot-put transfer",
                    value_transfer.span,
                    owner,
                ));
            }
        }
        let mut nested = Vec::with_capacity(arguments.len());
        for argument in arguments {
            nested.push(self.visit_expression(owner, declaration_span, argument)?);
        }
        let schedule = ArgumentSchedule {
            receiver: DirectEffect::Inert,
            arguments: direct
                .into_iter()
                .zip(nested.iter())
                .enumerate()
                .map(|(index, (direct, nested))| RankedArgument {
                    rank: index + 1,
                    nested: nested.clone(),
                    direct,
                })
                .collect(),
        };
        self.push_certificate(
            owner,
            declaration_span,
            expression.span,
            Boundary::Slot(operation.name()),
            schedule.clone(),
        )?;
        Ok(completed_boundary_effects(&schedule))
    }

    fn validate_call(
        &self,
        checked: &CheckedCallTransition,
        target: &CallTarget,
        expression: &Expr,
        arguments: &[Expr],
        receiver: Option<(&str, Span)>,
    ) -> Result<(), String> {
        let (parameters, expected_receiver, expected_result) = self.signature(target)?;
        if checked.arguments.len() != arguments.len()
            || parameters.len() != arguments.len()
            || expression.ty.as_ref() != Some(&expected_result)
        {
            return Err(schedule_mismatch(
                "call",
                checked.key.span,
                &checked.key.owner,
                "argument arity or result type differs from the typed target",
            ));
        }
        match (&checked.receiver, receiver, expected_receiver) {
            (None, None, None) => {}
            (Some(actual), Some((name, span)), Some((class, self_kind, expected_referent))) => {
                let unique = self_kind == SelfKind::Mut;
                if actual.class != class
                    || actual.transition.place != Place::local(name)
                    || actual.transition.span != span
                    || (actual.transition.effect == CallEffect::HavocUniqueBorrow) != unique
                    || actual.transition.referent != expected_referent
                {
                    return Err(schedule_mismatch(
                        "call receiver",
                        checked.key.span,
                        &checked.key.owner,
                        "receiver place, class, mutability, or span differs",
                    ));
                }
            }
            (Some(_), _, _) | (None, Some(_), _) | (None, None, Some(_)) => {
                return Err(schedule_mismatch(
                    "call receiver",
                    checked.key.span,
                    &checked.key.owner,
                    "receiver presence differs from the typed call",
                ));
            }
        }
        for (index, ((actual, parameter), expression)) in checked
            .arguments
            .iter()
            .zip(parameters.iter())
            .zip(arguments)
            .enumerate()
        {
            if actual.parameter_index != index
                || actual.parameter != parameter.name
                || actual.parameter_ty != parameter.ty
                || actual.argument_span != expression.span
            {
                return Err(schedule_mismatch(
                    "call argument",
                    checked.key.span,
                    &checked.key.owner,
                    "parameter identity, type, or span differs",
                ));
            }
            validate_argument_effect(&actual.effect, expression, &parameter.ty).map_err(
                |detail| {
                    schedule_mismatch(
                        "call argument",
                        checked.key.span,
                        &checked.key.owner,
                        &detail,
                    )
                },
            )?;
        }
        Ok(())
    }

    fn validate_sealed(
        &self,
        checked: &CheckedSealedOperation,
        target: CheckedSealedTarget,
        expression: &Expr,
        arguments: &[Expr],
    ) -> Result<(), String> {
        if checked.target != target
            || checked.key.span != expression.span
            || expression.ty.as_ref() != Some(&checked.result_ty)
            || checked.arguments.len() != arguments.len()
        {
            return Err(schedule_mismatch(
                "sealed operation",
                expression.span,
                &checked.key.owner,
                "target, result, or arity differs",
            ));
        }
        for (index, (actual, expression)) in checked.arguments.iter().zip(arguments).enumerate() {
            if actual.index != index
                || actual.argument_span != expression.span
                || expression.ty.as_ref() != Some(&actual.argument_ty)
            {
                return Err(schedule_mismatch(
                    "sealed argument",
                    checked.key.span,
                    &checked.key.owner,
                    "index, type, or span differs",
                ));
            }
            validate_argument_effect(&actual.effect, expression, &actual.argument_ty).map_err(
                |detail| {
                    schedule_mismatch(
                        "sealed argument",
                        checked.key.span,
                        &checked.key.owner,
                        &detail,
                    )
                },
            )?;
        }
        Ok(())
    }

    fn validate_slot(
        &self,
        checked: &CheckedSlotTransition,
        operation: &SlotOp,
        op_span: Span,
        expression: &Expr,
        arguments: &[Expr],
    ) -> Result<Vec<DirectEffect>, String> {
        let mismatch = |detail: &str| {
            schedule_mismatch(
                "owner-slot operation",
                expression.span,
                &checked.key.owner,
                detail,
            )
        };
        if checked.key.span != expression.span
            || checked.op_span != op_span
            || expression.ty.as_ref() != Some(&checked.result_ty)
            || arguments.len() != operation.arity()
        {
            return Err(mismatch(
                "operation span, result, expression span, or arity differs",
            ));
        }
        let mut direct = vec![DirectEffect::Inert; arguments.len()];
        match (&checked.kind, operation) {
            (
                CheckedSlotTransitionKind::Alloc {
                    length_ty,
                    length_span,
                },
                SlotOp::Alloc { elem },
            ) if arguments.first().is_some_and(|argument| {
                argument.span == *length_span && argument.ty.as_ref() == Some(length_ty)
            }) && *length_ty == Ty::Int(IntTy::U64)
                && checked.payload == *elem
                && checked.result_ty == Ty::slots(elem.clone()) => {}
            (
                CheckedSlotTransitionKind::Take {
                    container,
                    container_span,
                    index_ty,
                    index_span,
                },
                SlotOp::Take,
            ) if arguments
                .first()
                .is_some_and(|argument| argument.span == *container_span)
                && arguments.get(1).is_some_and(|argument| {
                    argument.span == *index_span && argument.ty.as_ref() == Some(index_ty)
                })
                && *index_ty == Ty::Int(IntTy::U64)
                && arguments[0].ty.as_ref()
                    == Some(&Ty::borrow(
                        Mutability::Mut,
                        Ty::slots(checked.payload.clone()),
                    ))
                && checked.result_ty == checked.payload =>
            {
                validate_slot_container(container, &arguments[0])
                    .map_err(|detail| mismatch(&detail))?;
                direct[0] = DirectEffect::Loan {
                    place: container.clone(),
                    unique: true,
                };
            }
            (
                CheckedSlotTransitionKind::Put {
                    container,
                    container_span,
                    index_ty,
                    index_span,
                    value_span,
                    value_transfer,
                },
                SlotOp::Put,
            ) if arguments
                .first()
                .is_some_and(|argument| argument.span == *container_span)
                && arguments.get(1).is_some_and(|argument| {
                    argument.span == *index_span && argument.ty.as_ref() == Some(index_ty)
                })
                && arguments.get(2).is_some_and(|argument| {
                    argument.span == *value_span && argument.ty.as_ref() == Some(&checked.payload)
                })
                && *index_ty == Ty::Int(IntTy::U64)
                && arguments[0].ty.as_ref()
                    == Some(&Ty::borrow(
                        Mutability::Mut,
                        Ty::slots(checked.payload.clone()),
                    ))
                && checked.result_ty == Ty::Unit =>
            {
                validate_slot_container(container, &arguments[0])
                    .map_err(|detail| mismatch(&detail))?;
                let expected_transfer = ValueTransferKey {
                    owner: checked.key.owner.clone(),
                    span: arguments[2].span,
                    sink: ValueTransferSink::SlotPut(container.clone()),
                };
                if *value_transfer != expected_transfer {
                    return Err(mismatch("linked slot-put transfer identity differs"));
                }
                let transfer = self
                    .ownership
                    .value_transfer(&expected_transfer)
                    .ok_or_else(|| mismatch("linked slot-put value transfer is missing"))?;
                validate_value_transfer(transfer, &arguments[2], &checked.payload)
                    .map_err(|detail| mismatch(&detail))?;
                direct[0] = DirectEffect::Loan {
                    place: container.clone(),
                    unique: true,
                };
                direct[2] = direct_value(transfer);
            }
            (CheckedSlotTransitionKind::Alloc { .. }, SlotOp::Take | SlotOp::Put)
            | (CheckedSlotTransitionKind::Take { .. }, SlotOp::Alloc { .. } | SlotOp::Put)
            | (CheckedSlotTransitionKind::Put { .. }, SlotOp::Alloc { .. } | SlotOp::Take)
            | (CheckedSlotTransitionKind::Alloc { .. }, SlotOp::Alloc { .. })
            | (CheckedSlotTransitionKind::Take { .. }, SlotOp::Take)
            | (CheckedSlotTransitionKind::Put { .. }, SlotOp::Put) => {
                return Err(mismatch("operation flavor or argument spans differ"));
            }
        }
        Ok(direct)
    }

    fn signature(
        &self,
        target: &CallTarget,
    ) -> Result<(&[Param], Option<(String, SelfKind, Ty)>, Ty), String> {
        match target {
            CallTarget::Function(name) => self
                .program
                .fns
                .iter()
                .chain(self.program.fn_templates.iter())
                .find(|function| function.name == *name)
                .map(|function| (function.params.as_slice(), None, function.ret.clone()))
                .ok_or_else(|| {
                    format!(
                        "internal.argument_schedule.target_missing: function `{name}` is absent"
                    )
                }),
            CallTarget::Constructor { class, init } => {
                let (class_decl, class_ty) = self.class_with_type(class)?;
                class_decl
                    .inits
                    .iter()
                    .find(|function| function.name == *init)
                    .map(|function| (function.params.as_slice(), None, class_ty))
                    .ok_or_else(|| format!("internal.argument_schedule.target_missing: constructor `{class}::{init}` is absent"))
            }
            CallTarget::Method { class, method } => {
                let (class_decl, class_ty) = self.class_with_type(class)?;
                class_decl
                    .methods
                    .iter()
                    .find(|candidate| candidate.f.name == *method)
                    .map(|candidate| {
                        (
                            candidate.f.params.as_slice(),
                            Some((class.clone(), candidate.self_kind, class_ty)),
                            candidate.f.ret.clone(),
                        )
                    })
                    .ok_or_else(|| format!("internal.argument_schedule.target_missing: method `{class}::{method}` is absent"))
            }
        }
    }

    fn class_with_type(&self, name: &str) -> Result<(&crate::ast::ClassDecl, Ty), String> {
        if let Some((index, class)) = self
            .program
            .classes
            .iter()
            .enumerate()
            .find(|(_, class)| class.name == name)
        {
            return Ok((class, Ty::Class(index)));
        }
        self.program
            .class_templates
            .iter()
            .enumerate()
            .find(|(_, class)| class.name == name)
            .map(|(index, class)| (class, Ty::Class(index)))
            .ok_or_else(|| {
                format!("internal.argument_schedule.target_missing: class `{name}` is absent")
            })
    }

    fn resolve_method_target(
        &self,
        owner: &CallOwner,
        expression: &Expr,
        method: &str,
    ) -> Result<CallTarget, String> {
        let target = self
            .ownership
            .calls
            .for_owner_span(owner, expression.span)
            .find_map(|(key, _)| match &key.target {
                CallTarget::Method {
                    class,
                    method: found,
                } if found == method => Some(CallTarget::Method {
                    class: class.clone(),
                    method: found.clone(),
                }),
                CallTarget::Function(_)
                | CallTarget::Constructor { .. }
                | CallTarget::Method { .. } => None,
            });
        target.ok_or_else(|| {
            format!(
                "internal.argument_schedule.call_missing: no resolved method `{method}` at {}..{}",
                expression.span.start, expression.span.end
            )
        })
    }

    fn push_certificate(
        &mut self,
        owner: &CallOwner,
        declaration_span: Span,
        span: Span,
        boundary: Boundary,
        schedule: ArgumentSchedule,
    ) -> Result<(), String> {
        if schedule.arguments.len() > MAX_ARGUMENTS {
            return Err(format!(
                "internal.argument_schedule.argument_bound: {} at {}..{} has {} arguments; certificate limit is {MAX_ARGUMENTS}",
                boundary.render(),
                span.start,
                span.end,
                schedule.arguments.len()
            ));
        }
        let nested: usize = schedule
            .arguments
            .iter()
            .map(|argument| argument.nested.len())
            .sum();
        if nested > MAX_NESTED_EFFECTS {
            return Err(format!(
                "internal.argument_schedule.effect_bound: {} at {}..{} has {nested} nested effects; certificate limit is {MAX_NESTED_EFFECTS}",
                boundary.render(),
                span.start,
                span.end
            ));
        }
        let start = span
            .start
            .checked_sub(declaration_span.start)
            .ok_or_else(|| {
                format!(
                    "internal.argument_schedule.identity: boundary span {}..{} precedes {}",
                    span.start,
                    span.end,
                    owner.render()
                )
            })?;
        let end = span
            .end
            .checked_sub(declaration_span.start)
            .ok_or_else(|| {
                format!(
                    "internal.argument_schedule.identity: boundary span {}..{} precedes {}",
                    span.start,
                    span.end,
                    owner.render()
                )
            })?;
        let owner_component = owner.certificate_component();
        let boundary_component = boundary.component();
        let occurrence = format!("{start}:{end}");
        let thm_name = injective_lean_components(
            "arg_schedule_cert",
            &[
                owner_component.as_str(),
                boundary_component.as_str(),
                occurrence.as_str(),
            ],
        );
        if !self.theorem_names.insert(thm_name.clone()) {
            return Err(format!(
                "internal.argument_schedule.identity_collision: {} at {}..{} duplicates a certificate identity inside {}",
                boundary.render(),
                span.start,
                span.end,
                owner.render()
            ));
        }
        self.certificates.push(ArgumentScheduleCertificate {
            name: format!(
                "argument_schedule.{}.{}.site.{start}-{end}",
                owner_component, boundary_component
            ),
            thm_name,
            span,
            boundary,
            schedule,
        });
        Ok(())
    }

    fn finish_owner(&self, owner: &CallOwner) -> Result<(), String> {
        if let Some((key, _)) = self
            .ownership
            .calls
            .for_owner(owner)
            .filter(|(key, _)| !self.visited_calls.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end, key.target.render()))
        {
            return Err(format!(
                "internal.argument_schedule.call_unvisited: checked record for {} at {}..{} inside {} was not visited",
                key.target.render(),
                key.span.start,
                key.span.end,
                owner.render()
            ));
        }
        if let Some((key, operation)) = self
            .ownership
            .sealed_operations_for_owner(owner)
            .filter(|(key, _)| !self.visited_sealed.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            return Err(format!(
                "internal.argument_schedule.sealed_unvisited: checked record for `{}` at {}..{} inside {} was not visited",
                operation.target.render(),
                key.span.start,
                key.span.end,
                owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .slot_transitions_for_owner(owner)
            .filter(|(key, _)| !self.visited_slots.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            return Err(format!(
                "internal.argument_schedule.slot_unvisited: checked owner-slot record at {}..{} inside {} was not visited",
                key.span.start,
                key.span.end,
                owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .option_takes_for_owner(owner)
            .filter(|(key, _)| !self.visited_option_takes.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end))
        {
            return Err(format!(
                "internal.argument_schedule.option_take_unvisited: checked option extraction at {}..{} inside {} was not visited",
                key.span.start,
                key.span.end,
                owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .value_transfers_for_owner(owner)
            .filter(|(key, _)| expression_internal_sink(&key.sink))
            .filter(|(key, _)| !self.visited_expression_transfers.contains(*key))
            .min_by_key(|(key, _)| (key.span.start, key.span.end, key.sink.render()))
        {
            return Err(format!(
                "internal.argument_schedule.value_transfer_unvisited: checked {} transfer at {}..{} inside {} was not visited",
                key.sink.render(),
                key.span.start,
                key.span.end,
                owner.render()
            ));
        }
        Ok(())
    }

    /// A per-real-owner finish cannot see a forged record retargeted to a
    /// phantom owner. Compare the complete relevant ownership tables after
    /// traversing every checked non-extern body. Dynamic tests and proof-reuse
    /// bodies emit the same closed theorem as every other checked body.
    fn finish_global(&self) -> Result<(), String> {
        if let Some((key, _)) = self
            .ownership
            .calls
            .iter()
            .filter(|(key, _)| !self.visited_calls.contains(*key))
            .min_by_key(|(key, _)| {
                (
                    key.owner.certificate_component(),
                    key.span.start,
                    key.span.end,
                    key.target.render(),
                )
            })
        {
            return Err(format!(
                "internal.argument_schedule.call_unvisited: checked record for {} at {}..{} inside {} was not visited by any typed body",
                key.target.render(),
                key.span.start,
                key.span.end,
                key.owner.render()
            ));
        }
        if let Some((key, operation)) = self
            .ownership
            .sealed_operations()
            .filter(|(key, _)| !self.visited_sealed.contains(*key))
            .min_by_key(|(key, _)| {
                (
                    key.owner.certificate_component(),
                    key.span.start,
                    key.span.end,
                )
            })
        {
            return Err(format!(
                "internal.argument_schedule.sealed_unvisited: checked record for `{}` at {}..{} inside {} was not visited by any typed body",
                operation.target.render(),
                key.span.start,
                key.span.end,
                key.owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .slot_transitions()
            .filter(|(key, _)| !self.visited_slots.contains(*key))
            .min_by_key(|(key, _)| {
                (
                    key.owner.certificate_component(),
                    key.span.start,
                    key.span.end,
                )
            })
        {
            return Err(format!(
                "internal.argument_schedule.slot_unvisited: checked owner-slot record at {}..{} inside {} was not visited by any typed body",
                key.span.start,
                key.span.end,
                key.owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .option_takes()
            .filter(|(key, _)| !self.visited_option_takes.contains(*key))
            .min_by_key(|(key, _)| {
                (
                    key.owner.certificate_component(),
                    key.span.start,
                    key.span.end,
                )
            })
        {
            return Err(format!(
                "internal.argument_schedule.option_take_unvisited: checked option extraction at {}..{} inside {} was not visited by any typed body",
                key.span.start,
                key.span.end,
                key.owner.render()
            ));
        }
        if let Some((key, _)) = self
            .ownership
            .value_transfers()
            .filter(|(key, _)| expression_internal_sink(&key.sink))
            .filter(|(key, _)| !self.visited_expression_transfers.contains(*key))
            .min_by_key(|(key, _)| {
                (
                    key.owner.certificate_component(),
                    key.span.start,
                    key.span.end,
                    key.sink.render(),
                )
            })
        {
            return Err(format!(
                "internal.argument_schedule.value_transfer_unvisited: checked {} transfer at {}..{} inside {} was not visited by any typed body",
                key.sink.render(),
                key.span.start,
                key.span.end,
                key.owner.render()
            ));
        }
        Ok(())
    }
}

/// Transfers that occur *inside* expression evaluation and can therefore be
/// hidden under an outer argument wrapper. Every other sink is a statement or
/// scope boundary and cannot run inside an expression in the current AST.
fn expression_internal_sink(sink: &ValueTransferSink) -> bool {
    match sink {
        ValueTransferSink::OptionPayload | ValueTransferSink::SlotPut(_) => true,
        ValueTransferSink::Binding(_)
        | ValueTransferSink::Assignment(_)
        | ValueTransferSink::Return
        | ValueTransferSink::FieldAssignment(_)
        | ValueTransferSink::DiscardTemporary
        | ValueTransferSink::SystemDeallocResource
        | ValueTransferSink::SystemDeallocRelease => false,
    }
}

fn validate_argument_effect(
    effect: &CallArgumentEffect,
    expression: &Expr,
    parameter_ty: &Ty,
) -> Result<(), String> {
    match (parameter_ty, effect) {
        (Ty::Borrow(mutability, referent), CallArgumentEffect::Loan(loan)) => {
            let explicit_borrow = BorrowedPlace::from_expr(expression);
            let explicit_mutability_matches = explicit_borrow
                .as_ref()
                .map_or(true, |borrowed| borrowed.mutability() == *mutability);
            let place = explicit_borrow
                .map(BorrowedPlace::into_place)
                .or_else(|| Place::from_value_expr(expression));
            let expected_effect = match mutability {
                Mutability::Shared => CallEffect::SharedLoan,
                Mutability::Mut => CallEffect::HavocUniqueBorrow,
            };
            if expression.ty.as_ref() != Some(parameter_ty)
                || place.as_ref() != Some(&loan.place)
                || loan.referent != **referent
                || loan.effect != expected_effect
                || loan.span != expression.span
                || !explicit_mutability_matches
            {
                Err("loan place, referent, mutability, type, or span differs".into())
            } else {
                Ok(())
            }
        }
        (Ty::Borrow(..), CallArgumentEffect::Value(_)) => {
            Err("borrowed parameter was recorded as a value".into())
        }
        (
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit,
            CallArgumentEffect::Value(value),
        ) => validate_value_transfer(value, expression, parameter_ty),
        (
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::Array(_)
            | Ty::Slots(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit,
            CallArgumentEffect::Loan(_),
        ) => Err("by-value parameter was recorded as a loan".into()),
    }
}

fn validate_value_transfer(
    transfer: &ValueTransfer,
    expression: &Expr,
    expected_ty: &Ty,
) -> Result<(), String> {
    let source = Place::from_value_expr(expression);
    let expected_kind = if expected_ty.is_affine() {
        if source.is_some() {
            ValueTransferKind::Move
        } else {
            ValueTransferKind::Fresh
        }
    } else {
        ValueTransferKind::Copy
    };
    if expression.ty.as_ref() != Some(expected_ty)
        || transfer.value_ty != *expected_ty
        || transfer.span != expression.span
        || transfer.source != source
        || transfer.kind != expected_kind
    {
        Err("value source, type, transfer kind, or span differs".into())
    } else {
        Ok(())
    }
}

fn validate_slot_container(place: &Place, expression: &Expr) -> Result<(), String> {
    let borrowed = BorrowedPlace::from_expr(expression)
        .ok_or_else(|| "owner-slot container has no explicit borrowed place".to_string())?;
    if borrowed.place() != place || borrowed.mutability() != Mutability::Mut {
        Err("owner-slot container place or mutability differs".into())
    } else {
        Ok(())
    }
}

fn schedule_mismatch(kind: &str, span: Span, owner: &CallOwner, detail: &str) -> String {
    format!(
        "internal.argument_schedule.record_mismatch: {kind} at {}..{} inside {}: {detail}",
        span.start,
        span.end,
        owner.render()
    )
}

fn duplicate_visit(kind: &str, span: Span, owner: &CallOwner) -> String {
    format!(
        "internal.argument_schedule.duplicate_visit: {kind} at {}..{} inside {} consumed one checked identity more than once",
        span.start,
        span.end,
        owner.render()
    )
}

fn direct_loan(transition: &crate::transition::CallTransition) -> DirectEffect {
    DirectEffect::Loan {
        place: transition.place.clone(),
        unique: transition.effect == CallEffect::HavocUniqueBorrow,
    }
}

fn direct_value(value: &ValueTransfer) -> DirectEffect {
    match (value.kind, value.source.as_ref()) {
        (ValueTransferKind::Move, Some(place)) => DirectEffect::Move {
            place: place.clone(),
        },
        (ValueTransferKind::Copy | ValueTransferKind::Fresh, _)
        | (ValueTransferKind::Move, None) => DirectEffect::Inert,
    }
}

fn direct_effect(effect: &CallArgumentEffect) -> DirectEffect {
    match effect {
        CallArgumentEffect::Loan(loan) => direct_loan(loan),
        CallArgumentEffect::Value(value) => direct_value(value),
    }
}

fn completed_boundary_effects(schedule: &ArgumentSchedule) -> Vec<NestedEffect> {
    let mut completed = Vec::new();
    for argument in &schedule.arguments {
        completed.extend(argument.nested.clone());
        if let DirectEffect::Move { place } = &argument.direct {
            completed.push(NestedEffect::Move(place.clone()));
        }
    }
    if let DirectEffect::Loan {
        place,
        unique: true,
    } = &schedule.receiver
    {
        completed.push(NestedEffect::Write(place.clone()));
    }
    for argument in &schedule.arguments {
        if let DirectEffect::Loan {
            place,
            unique: true,
        } = &argument.direct
        {
            completed.push(NestedEffect::Write(place.clone()));
        }
    }
    completed
}

fn lean_schedule(schedule: &ArgumentSchedule) -> String {
    let arguments = schedule
        .arguments
        .iter()
        .map(lean_argument)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "({{ receiver := {}, arguments := [{arguments}] }} : Sable.ArgumentSchedule.Schedule)",
        lean_direct(&schedule.receiver)
    )
}

fn lean_argument(argument: &RankedArgument) -> String {
    let nested = argument
        .nested
        .iter()
        .map(lean_nested)
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "{{ rank := {}, nested := [{nested}], direct := {} }}",
        argument.rank,
        lean_direct(&argument.direct)
    )
}

fn lean_direct(effect: &DirectEffect) -> String {
    match effect {
        DirectEffect::Inert => "Sable.ArgumentSchedule.DirectEffect.inert".into(),
        DirectEffect::Loan { place, unique } => format!(
            "Sable.ArgumentSchedule.DirectEffect.loan {} {}",
            lean_place(place),
            unique
        ),
        DirectEffect::Move { place } => format!(
            "Sable.ArgumentSchedule.DirectEffect.move {}",
            lean_place(place)
        ),
    }
}

fn lean_nested(effect: &NestedEffect) -> String {
    match effect {
        NestedEffect::Write(place) => format!(
            "Sable.ArgumentSchedule.NestedEffect.write {}",
            lean_place(place)
        ),
        NestedEffect::Move(place) => format!(
            "Sable.ArgumentSchedule.NestedEffect.move {}",
            lean_place(place)
        ),
    }
}

fn lean_place(place: &Place) -> String {
    let fields = place
        .fields()
        .iter()
        .map(|field| lean_string(field))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "({{ root := {}, fields := [{fields}] }} : Sable.ArgumentSchedule.Place)",
        lean_string(place.root())
    )
}

fn lean_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for character in value.chars() {
        match character {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

fn injective_lean_name(prefix: &str, identity: &str) -> String {
    let payload = identity
        .as_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    format!("{prefix}_v1_{}_{payload}", identity.len())
}

fn injective_lean_components(prefix: &str, components: &[&str]) -> String {
    let identity = components
        .iter()
        .map(|component| format!("{}:{component}", component.len()))
        .collect::<String>();
    injective_lean_name(prefix, &identity)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::{
        WEAKEN_ARGUMENT_MOVE_CONFLICT, WEAKEN_ARGUMENT_PENDING_MUTATION,
        WEAKEN_ARGUMENT_UNIQUE_CONFLICT,
    };
    use crate::span::LineMap;
    use crate::vcgen::VcResult;
    use std::collections::HashSet;
    use std::path::Path;
    use std::sync::atomic::{AtomicU64, Ordering};

    static LEAN_TEST_NONCE: AtomicU64 = AtomicU64::new(0);

    fn parsed_program(source: &str) -> Program {
        let scanned = crate::scan::scan(source);
        let tokens = crate::lexer::lex(&scanned.program_text).expect("test source should lex");
        crate::parser::parse(
            &tokens,
            &scanned.blocks,
            &LineMap::new(source),
            &scanned.program_text,
        )
        .expect("test source should parse")
    }

    fn checked_program(source: &str) -> (Program, crate::check::CheckResult) {
        let mut program = parsed_program(source);
        crate::mono::monomorphize(&mut program).expect("test source should monomorphize");
        let checked = crate::check::check(&mut program).expect("test source should typecheck");
        (program, checked)
    }

    fn weakened_generation(source: &str, weakening: u8) -> VcResult {
        let mut program = parsed_program(source);
        crate::mono::monomorphize(&mut program).expect("historical source should monomorphize");
        let checked = crate::check::with_argument_schedule_test_weakening(weakening, || {
            crate::check::check(&mut program)
        })
        .expect("the deliberately weakened checker should admit the historical witness");
        crate::vcgen::generate(&program, &checked, source, Path::new("."))
            .expect("post-check schedule extraction should preserve the invalid closed trace")
    }

    fn certificate_only(mut generated: VcResult) -> VcResult {
        generated.ghosts.clear();
        generated.classes.clear();
        generated.records.clear();
        generated.clause_wfs.clear();
        generated.obligations.clear();
        generated.transition_certificates.clear();
        generated
    }

    fn lean_diagnostics(
        source: &str,
        generated: &VcResult,
        label: &str,
    ) -> Vec<crate::diag::Diagnostic> {
        let emitted = crate::lean::emit(
            generated,
            &[],
            &HashSet::new(),
            &[],
            &crate::lean::EmittedNames::default(),
        );
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("compiler crate has a repository parent");
        let environment = crate::lean::ProofEnvironment::capture(repo_root)
            .expect("the repository proof environment must be capturable");
        let nonce = LEAN_TEST_NONCE.fetch_add(1, Ordering::Relaxed);
        let lean_file = std::env::temp_dir().join(format!(
            "sable_argument_schedule_{}_{}_{}.lean",
            crate::vcgen::sanitize(label),
            std::process::id(),
            nonce
        ));
        std::fs::write(&lean_file, &emitted.lean_source)
            .expect("the generated certificate document must be writable");
        let messages = crate::lean::run_lean(
            repo_root,
            &environment,
            &lean_file,
            None,
            &emitted.lean_source,
        )
        .expect("Lean should check the closed certificate document");
        let _ = std::fs::remove_file(&lean_file);
        let modules = crate::modules::ModuleSet::single(format!("{label}.sable"), source.into());
        crate::lean::diagnose(&emitted, generated, &messages, &modules)
    }

    fn assert_historical_rejected(source: &str, weakening: u8, label: &str) {
        let generated = certificate_only(weakened_generation(source, weakening));
        assert!(
            !generated.argument_schedule_certificates.is_empty(),
            "{label}: the weakened checker produced no schedule evidence"
        );
        let diagnostics = lean_diagnostics(source, &generated, label);
        assert!(
            !diagnostics.is_empty(),
            "{label}: Lean accepted every weakened-checker schedule"
        );
        assert!(
            diagnostics.iter().all(|diagnostic| {
                diagnostic.name == "internal.argument_schedule_certificate_rejected"
                    && diagnostic.title.contains("argument-schedule")
                    && diagnostic.label.contains("not alias-safe")
            }),
            "{label}: {diagnostics:#?}"
        );
    }

    #[test]
    fn historical_vf03_vf08_vf09_and_ai08_are_rejected_by_lean_when_checker_guards_are_weakened() {
        assert_historical_rejected(
            include_str!("../../corpus/must-fail/borrow_conflict.sable"),
            WEAKEN_ARGUMENT_UNIQUE_CONFLICT,
            "vf03_unique_shared_alias",
        );
        assert_historical_rejected(
            include_str!("../../corpus/must-fail/borrow_moved_in_call.sable"),
            WEAKEN_ARGUMENT_MOVE_CONFLICT,
            "vf08_direct_move_and_loan",
        );
        assert_historical_rejected(
            include_str!("../../corpus/must-fail/borrow_conflict_nested_mutation.sable"),
            WEAKEN_ARGUMENT_PENDING_MUTATION,
            "vf09_pending_loan_later_write",
        );
        assert_historical_rejected(
            include_str!("../../corpus/must-fail/borrow_moved_in_sealed_nested.sable"),
            WEAKEN_ARGUMENT_MOVE_CONFLICT,
            "ai08_sealed_pending_loan_later_move",
        );
    }

    #[test]
    fn checker_weakening_hooks_are_statically_confined_to_test_builds() {
        let checker = include_str!("check.rs");
        for declaration in [
            "pub(crate) const WEAKEN_ARGUMENT_UNIQUE_CONFLICT",
            "pub(crate) const WEAKEN_ARGUMENT_MOVE_CONFLICT",
            "pub(crate) const WEAKEN_ARGUMENT_PENDING_MUTATION",
            "thread_local!",
            "pub(crate) fn with_argument_schedule_test_weakening",
            "fn argument_schedule_test_weakened",
        ] {
            let offset = checker
                .find(declaration)
                .unwrap_or_else(|| panic!("missing mutation-harness declaration `{declaration}`"));
            let prefix = &checker[..offset];
            assert_eq!(
                prefix.lines().rev().find(|line| !line.trim().is_empty()),
                Some("#[cfg(test)]"),
                "`{declaration}` is not guarded by cfg(test)"
            );
        }
        let lines: Vec<&str> = checker.lines().collect();
        assert_eq!(
            lines
                .windows(2)
                .filter(|window| {
                    window[0].trim() == "#[cfg(test)]"
                        && window[1]
                            .trim()
                            .starts_with("if argument_schedule_test_weakened(")
                })
                .count(),
            5,
            "every bypass branch must remain individually compiled out of production"
        );
        assert!(
            !checker.contains("#[cfg(not(test))]\nfn argument_schedule_test_weakened")
                && !checker.contains("#[cfg(not(test))]\nconst WEAKEN_ARGUMENT"),
            "production must not contain a dormant weakening helper or flag"
        );
    }

    const SHARED_CALL: &str = r#"
fn observe(&[u8] left, &[u8] right) -> u8 {
    return left[0] + right[0];
}

fn subject() -> u8 {
    mut [u8] values = alloc_array<u8>(1, 1);
    return observe(&values, &values);
}
"#;

    #[test]
    fn tampering_a_valid_shared_schedule_to_unique_is_rejected_and_cannot_be_skipped() {
        let (program, checked) = checked_program(SHARED_CALL);
        let mut generated = certificate_only(
            crate::vcgen::generate(&program, &checked, SHARED_CALL, Path::new("."))
                .expect("the shared/shared call should generate"),
        );
        let certificate = generated
            .argument_schedule_certificates
            .iter_mut()
            .find(|certificate| certificate.boundary().contains("observe"))
            .expect("the observed call has a schedule certificate");
        let DirectEffect::Loan { unique, .. } = &mut certificate.schedule.arguments[0].direct
        else {
            panic!("the first observed argument is a loan")
        };
        *unique = true;

        let certificate_name = certificate.name.clone();
        let theorem_name = certificate.thm_name.clone();

        let attempted_skip = HashSet::from([certificate_name]);
        let emitted = crate::lean::emit(
            &generated,
            &[],
            &attempted_skip,
            &[],
            &crate::lean::EmittedNames::default(),
        );
        assert!(emitted.lean_source.contains(&theorem_name));
        assert!(emitted.lean_source.contains("by decide"));

        let diagnostics = lean_diagnostics(SHARED_CALL, &generated, "tampered_unique");
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].name,
            "internal.argument_schedule_certificate_rejected"
        );
    }

    #[test]
    fn maximum_bounded_disjoint_schedule_reduces_under_the_generated_lean_budget() {
        let (program, checked) = checked_program(SHARED_CALL);
        let mut generated = certificate_only(
            crate::vcgen::generate(&program, &checked, SHARED_CALL, Path::new("."))
                .expect("the shared-call seed should generate"),
        );
        let certificate = generated
            .argument_schedule_certificates
            .first_mut()
            .expect("the seed has one schedule certificate");
        let nested: Vec<NestedEffect> = (0..MAX_NESTED_EFFECTS)
            .map(|index| NestedEffect::Move(Place::local(&format!("nested_{index}"))))
            .collect();
        certificate.schedule = ArgumentSchedule {
            receiver: DirectEffect::Inert,
            arguments: (0..MAX_ARGUMENTS)
                .map(|index| RankedArgument {
                    rank: index + 1,
                    nested: if index == 0 {
                        nested.clone()
                    } else {
                        Vec::new()
                    },
                    direct: DirectEffect::Move {
                        place: Place::local(&format!("direct_{index}")),
                    },
                })
                .collect(),
        };

        let diagnostics = lean_diagnostics(SHARED_CALL, &generated, "maximum_safe_schedule");
        assert!(
            diagnostics.is_empty(),
            "the admitted maxima must kernel-reduce under ordinary generated options: {diagnostics:#?}"
        );
    }

    #[test]
    fn exact_record_mismatch_and_phantom_owner_records_fail_closed() {
        let (program, mut checked) = checked_program(SHARED_CALL);
        let key = checked
            .ownership
            .calls
            .for_owner(&CallOwner::Function("subject".into()))
            .next()
            .map(|(key, _)| key.clone())
            .expect("subject has one call");
        checked
            .ownership
            .calls
            .get_mut(&key)
            .expect("record remains present")
            .arguments[0]
            .argument_span = Span::new(0, 0);
        let mismatch = extract(&program, &checked.ownership)
            .expect_err("an exact call-record mismatch must fail closed");
        assert!(
            mismatch.starts_with("internal.argument_schedule.record_mismatch:"),
            "{mismatch}"
        );

        let (program, mut checked) = checked_program(SHARED_CALL);
        let mut phantom = checked
            .ownership
            .calls
            .for_owner(&CallOwner::Function("subject".into()))
            .next()
            .map(|(_, call)| call.clone())
            .expect("subject has one call");
        phantom.key.owner = CallOwner::Function("phantom_owner".into());
        checked
            .ownership
            .calls
            .insert(phantom)
            .expect("the phantom key is distinct");
        let unvisited = extract(&program, &checked.ownership)
            .expect_err("global completeness must find a phantom-owner record");
        assert!(
            unvisited.starts_with("internal.argument_schedule.call_unvisited:"),
            "{unvisited}"
        );
        assert!(unvisited.contains("phantom_owner"), "{unvisited}");

        let (program, mut checked) = checked_program(SHARED_CALL);
        let key = checked
            .ownership
            .calls
            .for_owner(&CallOwner::Function("subject".into()))
            .next()
            .map(|(key, _)| key.clone())
            .expect("subject has one call");
        checked
            .ownership
            .calls
            .get_mut(&key)
            .expect("record remains under its original table key")
            .key
            .target = CallTarget::Function("retargeted".into());
        let embedded = extract(&program, &checked.ownership)
            .expect_err("an embedded call key cannot disagree with its table identity");
        assert!(
            embedded.starts_with("internal.argument_schedule.record_mismatch:")
                && embedded.contains("embedded record key"),
            "{embedded}"
        );
    }

    #[test]
    fn typed_result_annotations_and_explicit_borrow_mutability_fail_closed() {
        let (mut program, checked) = checked_program(SHARED_CALL);
        let subject = program
            .fns
            .iter_mut()
            .find(|function| function.name == "subject")
            .expect("subject function");
        let Stmt::Return {
            value: Some(call), ..
        } = subject.body.last_mut().expect("subject return")
        else {
            panic!("subject ends in a valued return")
        };
        call.ty = None;
        let missing_result = extract(&program, &checked.ownership)
            .expect_err("a call without its checked result annotation must fail closed");
        assert!(
            missing_result.starts_with("internal.argument_schedule.record_mismatch:")
                && missing_result.contains("result type"),
            "{missing_result}"
        );

        let (mut program, checked) = checked_program(SHARED_CALL);
        let subject = program
            .fns
            .iter_mut()
            .find(|function| function.name == "subject")
            .expect("subject function");
        let Stmt::Return {
            value: Some(call), ..
        } = subject.body.last_mut().expect("subject return")
        else {
            panic!("subject ends in a valued return")
        };
        let ExprKind::Call { args, .. } = &mut call.kind else {
            panic!("subject returns a call")
        };
        let ExprKind::Borrow { mutable, .. } = &mut args[0].kind else {
            panic!("the first argument is an explicit borrow")
        };
        *mutable = true;
        let wrong_borrow = extract(&program, &checked.ownership)
            .expect_err("the explicit borrow node cannot disagree with the shared parameter");
        assert!(
            wrong_borrow.starts_with("internal.argument_schedule.record_mismatch:")
                && wrong_borrow.contains("mutability"),
            "{wrong_borrow}"
        );

        let (mut program, checked) = checked_program(SLOT_BOUNDARIES);
        let slot_boundary = program
            .fns
            .iter_mut()
            .find(|function| function.name == "slot_boundary")
            .expect("slot boundary function");
        let slot_put = slot_boundary
            .body
            .iter_mut()
            .find_map(|statement| {
                let Stmt::ExprStmt(expression) = statement else {
                    return None;
                };
                matches!(
                    expression.kind,
                    ExprKind::SlotOp {
                        op: SlotOp::Put,
                        ..
                    }
                )
                .then_some(expression)
            })
            .expect("slot-put expression");
        slot_put.ty = None;
        let missing_unit = extract(&program, &checked.ownership)
            .expect_err("a Unit slot operation still requires its checked result annotation");
        assert!(
            missing_unit.starts_with("internal.argument_schedule.record_mismatch:")
                && missing_unit.contains("result"),
            "{missing_unit}"
        );
    }

    #[test]
    fn sealed_embedded_record_keys_are_reconciled_with_the_table_identity() {
        let source = include_str!("../../corpus/verifies/unsafe_copy.sable");
        let (program, mut checked) = checked_program(source);
        let key = checked
            .ownership
            .sealed_operations()
            .next()
            .map(|(key, _)| key.clone())
            .expect("the raw-memory fixture has a sealed operation");
        checked
            .ownership
            .sealed_operation_mut(&key)
            .expect("record remains under its original table key")
            .key
            .owner = CallOwner::Function("retargeted".into());
        let embedded = extract(&program, &checked.ownership)
            .expect_err("an embedded sealed key cannot disagree with its table identity");
        assert!(
            embedded.starts_with("internal.argument_schedule.record_mismatch:")
                && embedded.contains("embedded record key"),
            "{embedded}"
        );
    }

    #[test]
    fn owning_some_payload_moves_are_exactly_visited() {
        let source = include_str!("../../corpus/verifies/affine_option_class.sable");
        let (program, mut checked) = checked_program(source);
        extract(&program, &checked.ownership)
            .expect("every owning `some` payload transfer should be visited");
        let key = checked
            .ownership
            .value_transfers()
            .find(|(key, transfer)| {
                key.sink == ValueTransferSink::OptionPayload
                    && transfer.kind == ValueTransferKind::Move
                    && transfer.source.is_some()
            })
            .map(|(key, _)| key.clone())
            .expect("the fixture wraps a named class owner in `some`");
        checked
            .ownership
            .remove_value_transfer(&key)
            .expect("remove the exact OptionPayload move");
        let missing = extract(&program, &checked.ownership)
            .expect_err("an omitted owning `some` move must fail closed");
        assert!(
            missing.starts_with("internal.argument_schedule.option_payload_missing:"),
            "{missing}"
        );
    }

    #[test]
    fn duplicate_ast_consumption_cannot_reuse_any_checked_expression_identity() {
        let (mut program, checked) = checked_program(SHARED_CALL);
        let subject = program
            .fns
            .iter_mut()
            .find(|function| function.name == "subject")
            .expect("subject function");
        subject
            .body
            .push(subject.body.last().expect("call statement").clone());
        let duplicate = extract(&program, &checked.ownership)
            .expect_err("one call record cannot certify two AST occurrences");
        assert!(
            duplicate.starts_with("internal.argument_schedule.duplicate_visit: call"),
            "{duplicate}"
        );

        let source = include_str!("../../corpus/verifies/unsafe_copy.sable");
        let (mut program, checked) = checked_program(source);
        let first_byte = program
            .fns
            .iter_mut()
            .find(|function| function.name == "first_byte")
            .expect("first_byte function");
        let exposure = first_byte
            .body
            .iter()
            .find(|statement| matches!(statement, Stmt::Expose { .. }))
            .expect("raw-load exposure")
            .clone();
        first_byte.body.push(exposure);
        let duplicate = extract(&program, &checked.ownership)
            .expect_err("one sealed record cannot certify two AST occurrences");
        assert!(
            duplicate.starts_with("internal.argument_schedule.duplicate_visit: sealed operation"),
            "{duplicate}"
        );

        let (mut program, checked) = checked_program(SLOT_BOUNDARIES);
        let slot_boundary = program
            .fns
            .iter_mut()
            .find(|function| function.name == "slot_boundary")
            .expect("slot boundary function");
        slot_boundary
            .body
            .push(slot_boundary.body.first().expect("slot allocation").clone());
        let duplicate = extract(&program, &checked.ownership)
            .expect_err("one slot record cannot certify two AST occurrences");
        assert!(
            duplicate
                .starts_with("internal.argument_schedule.duplicate_visit: owner-slot operation"),
            "{duplicate}"
        );

        let (mut program, mut checked) = checked_program(SLOT_BOUNDARIES);
        let put_key = slot_key(&checked, |kind| {
            matches!(kind, CheckedSlotTransitionKind::Put { .. })
        });
        let mut second_put = checked
            .ownership
            .slot_transition(&put_key)
            .expect("original put transition")
            .clone();
        let second_span = Span::new(0, 0);
        second_put.key.span = second_span;
        checked
            .ownership
            .insert_slot_transition(second_put)
            .expect("the forged second put has a distinct boundary key");
        let slot_boundary = program
            .fns
            .iter_mut()
            .find(|function| function.name == "slot_boundary")
            .expect("slot boundary function");
        let mut put_statement = slot_boundary
            .body
            .iter()
            .find(|statement| {
                matches!(
                    statement,
                    Stmt::ExprStmt(Expr {
                        kind: ExprKind::SlotOp {
                            op: SlotOp::Put,
                            ..
                        },
                        ..
                    })
                )
            })
            .expect("put statement")
            .clone();
        let Stmt::ExprStmt(expression) = &mut put_statement else {
            unreachable!()
        };
        expression.span = second_span;
        slot_boundary.body.push(put_statement);
        let duplicate = extract(&program, &checked.ownership)
            .expect_err("two slot boundaries cannot share one SlotPut transfer identity");
        assert!(
            duplicate.starts_with("internal.argument_schedule.duplicate_visit: slot-put transfer"),
            "{duplicate}"
        );

        let source = include_str!("../../corpus/verifies/affine_option_class.sable");
        let (mut program, checked) = checked_program(source);
        let take_and_use = program
            .fns
            .iter_mut()
            .find(|function| function.name == "take_and_use")
            .expect("take fixture");
        let Stmt::If { then_block, .. } = &mut take_and_use.body[1] else {
            panic!("the take fixture has its guarded extraction second")
        };
        then_block.push(then_block.first().expect("option take").clone());
        let duplicate = extract(&program, &checked.ownership)
            .expect_err("one option-take record cannot certify two AST occurrences");
        assert!(
            duplicate.starts_with("internal.argument_schedule.duplicate_visit: option extraction"),
            "{duplicate}"
        );

        let (mut program, checked) = checked_program(source);
        let wrap_named = program
            .fns
            .iter_mut()
            .find(|function| function.name == "wrap_named")
            .expect("named payload fixture");
        wrap_named.body.push(wrap_named.body[1].clone());
        let duplicate = extract(&program, &checked.ownership)
            .expect_err("one OptionPayload record cannot certify two AST occurrences");
        assert!(
            duplicate
                .starts_with("internal.argument_schedule.duplicate_visit: option-payload transfer"),
            "{duplicate}"
        );
    }

    #[test]
    fn method_receiver_referent_matches_the_exact_resolved_class() {
        let source = r#"
class Alpha {
    u64 value;

    init make() {
        self.value = 1;
    }

    fn read(&self) -> u64 {
        return self.value;
    }
}

class Beta {
    u64 value;

    init make() {
        self.value = 2;
    }
}

fn subject() -> u64 {
    var alpha = Alpha::make();
    return alpha.read();
}
"#;
        let (program, mut checked) = checked_program(source);
        let other_class = program
            .classes
            .iter()
            .position(|class| class.name == "Beta")
            .expect("Beta class index");
        let key = checked
            .ownership
            .calls
            .for_owner(&CallOwner::Function("subject".into()))
            .find(|(key, _)| matches!(key.target, CallTarget::Method { .. }))
            .map(|(key, _)| key.clone())
            .expect("method call record");
        checked
            .ownership
            .calls
            .get_mut(&key)
            .expect("method call record")
            .receiver
            .as_mut()
            .expect("method receiver")
            .transition
            .referent = Ty::Class(other_class);
        let mismatch = extract(&program, &checked.ownership)
            .expect_err("a merely class-shaped receiver referent is not exact enough");
        assert!(
            mismatch.starts_with("internal.argument_schedule.record_mismatch:")
                && mismatch.contains("call receiver"),
            "{mismatch}"
        );
    }

    #[test]
    fn checked_tests_and_proof_reusing_instances_still_emit_closed_schedules() {
        let source = r#"
fn observe(u64 value) {
}

class GenericBox<T> {
    T value;

    init make(T value) {
        self.value = value;
    }

    fn ping(&self) {
        observe(1);
    }
}

fn subject() {
    var box = GenericBox<u64>::make(1);
    box.ping();
}

fn test_schedule() {
    observe(2);
}
"#;
        let (program, checked) = checked_program(source);
        let reused = program
            .classes
            .iter()
            .find(|class| {
                matches!(
                    class.proof_reuse,
                    crate::ast::ProofReuse::Adr0009IntModel(_)
                )
            })
            .expect("the u64 generic instance uses its integer-model proof");
        let certificates = extract(&program, &checked.ownership)
            .expect("all checked non-extern schedules should extract");
        assert!(
            certificates.iter().any(|certificate| certificate
                .name
                .contains(&format!("method.{}.ping", reused.name))),
            "the proof-reusing concrete method still needs a closed schedule theorem"
        );
        assert!(
            certificates
                .iter()
                .any(|certificate| certificate.name.contains("function.test_schedule")),
            "a checked dynamic test body still needs its closed schedule theorem"
        );
    }

    #[test]
    fn certificate_names_are_length_framed_and_collision_safe() {
        let left = injective_lean_components("arg_schedule_cert", &["a", "bc"]);
        let right = injective_lean_components("arg_schedule_cert", &["ab", "c"]);
        assert_ne!(left, right);
        assert!(
            left.chars()
                .all(|character| character.is_ascii_alphanumeric() || character == '_')
        );

        let (program, checked) = checked_program(SHARED_CALL);
        let certificates = extract(&program, &checked.ownership)
            .expect("the real schedule identities should be unique");
        let names: HashSet<&str> = certificates
            .iter()
            .map(|certificate| certificate.thm_name.as_str())
            .collect();
        assert_eq!(names.len(), certificates.len());
    }

    const SLOT_BOUNDARIES: &str = r#"
fn slot_boundary(u64 value) -> u64 {
    mut slots<u64> cells = alloc_slots<u64>(1);
    slot_put(&mut cells, 0, value);
    return slot_take(&mut cells, 0);
}
"#;

    fn slot_key(
        checked: &crate::check::CheckResult,
        predicate: impl Fn(&CheckedSlotTransitionKind) -> bool,
    ) -> EffectSiteKey {
        checked
            .ownership
            .slot_transitions_for_owner(&CallOwner::Function("slot_boundary".into()))
            .find(|(_, transition)| predicate(&transition.kind))
            .map(|(key, _)| key.clone())
            .expect("the requested slot boundary exists")
    }

    fn assert_slot_tamper_rejected(tamper: impl FnOnce(&mut crate::check::CheckResult)) -> String {
        let (program, mut checked) = checked_program(SLOT_BOUNDARIES);
        tamper(&mut checked);
        let error = extract(&program, &checked.ownership)
            .expect_err("the coordinated owner-slot record tamper must fail closed");
        assert!(
            error.starts_with("internal.argument_schedule.record_mismatch:"),
            "{error}"
        );
        error
    }

    #[test]
    fn owner_slot_record_fields_and_linked_transfer_identity_are_exact() {
        assert_slot_tamper_rejected(|checked| {
            let key = slot_key(checked, |kind| {
                matches!(kind, CheckedSlotTransitionKind::Alloc { .. })
            });
            checked
                .ownership
                .slot_transition_mut(&key)
                .expect("record remains under its original table key")
                .key
                .owner = CallOwner::Function("retargeted".into());
        });

        assert_slot_tamper_rejected(|checked| {
            let key = slot_key(checked, |kind| {
                matches!(kind, CheckedSlotTransitionKind::Alloc { .. })
            });
            checked
                .ownership
                .slot_transition_mut(&key)
                .expect("alloc transition")
                .op_span = Span::new(0, 0);
        });

        assert_slot_tamper_rejected(|checked| {
            let key = slot_key(checked, |kind| {
                matches!(kind, CheckedSlotTransitionKind::Alloc { .. })
            });
            checked
                .ownership
                .slot_transition_mut(&key)
                .expect("alloc transition")
                .payload = Ty::Bool;
        });

        assert_slot_tamper_rejected(|checked| {
            let key = slot_key(checked, |kind| {
                matches!(kind, CheckedSlotTransitionKind::Alloc { .. })
            });
            let CheckedSlotTransitionKind::Alloc { length_ty, .. } = &mut checked
                .ownership
                .slot_transition_mut(&key)
                .expect("alloc transition")
                .kind
            else {
                unreachable!()
            };
            *length_ty = Ty::Bool;
        });

        assert_slot_tamper_rejected(|checked| {
            let key = slot_key(checked, |kind| {
                matches!(kind, CheckedSlotTransitionKind::Take { .. })
            });
            let CheckedSlotTransitionKind::Take { index_ty, .. } = &mut checked
                .ownership
                .slot_transition_mut(&key)
                .expect("take transition")
                .kind
            else {
                unreachable!()
            };
            *index_ty = Ty::Bool;
        });

        let linked_identity = assert_slot_tamper_rejected(|checked| {
            let key = slot_key(checked, |kind| {
                matches!(kind, CheckedSlotTransitionKind::Put { .. })
            });
            let original_key = match &checked
                .ownership
                .slot_transition(&key)
                .expect("put transition")
                .kind
            {
                CheckedSlotTransitionKind::Put { value_transfer, .. } => value_transfer.clone(),
                CheckedSlotTransitionKind::Alloc { .. }
                | CheckedSlotTransitionKind::Take { .. } => unreachable!(),
            };
            let transfer = checked
                .ownership
                .value_transfer(&original_key)
                .expect("linked transfer")
                .clone();
            let forged_key = ValueTransferKey {
                owner: original_key.owner.clone(),
                span: original_key.span,
                sink: ValueTransferSink::OptionPayload,
            };
            checked
                .ownership
                .insert_value_transfer(forged_key.owner.clone(), forged_key.sink.clone(), transfer)
                .expect("the forged sink is a distinct retained record");
            let CheckedSlotTransitionKind::Put { value_transfer, .. } = &mut checked
                .ownership
                .slot_transition_mut(&key)
                .expect("put transition")
                .kind
            else {
                unreachable!()
            };
            *value_transfer = forged_key;
        });
        assert!(
            linked_identity.contains("transfer identity differs"),
            "{linked_identity}"
        );
    }
}
