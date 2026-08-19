//! Shared structural control-flow facts over the checked statement tree.
//!
//! [`ControlOutline`] is the pre-check structural authority for lexical blocks,
//! parentage, and normal/return reachability. It is deliberately total over an
//! untyped parser AST: source diagnostics run before stable-key collisions or
//! typed cleanup details are sealed. [`BodyPlan`] enriches that exact outline
//! with typed lexical scopes, conditional drop identities, ordered exit routes,
//! replacement actions, exact source trap sites, and concrete-class
//! destruction recipes. The result is a structured control plan rather than an
//! expression CFG; dynamic liveness and representation remain consumer state
//! (ADR 0086).

use crate::ast::{
    BinOp, ClassDecl, Expr, ExprKind, IntTy, Mutability, Param, Program, RawOp, ResKind, ResOp,
    Stmt, Ty, UnOp,
};
use crate::ownership::{EffectSiteKey, ValueTransferKey, ValueTransferSink};
use crate::place::Place;
use crate::scan::{Clause, ClauseKind};
use crate::span::Span;
use crate::transition::CallOwner;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FlowSummary {
    reaches_next: bool,
    has_reachable_return: bool,
    contains_return: bool,
}

impl FlowSummary {
    const FALLTHROUGH: Self = Self {
        reaches_next: true,
        has_reachable_return: false,
        contains_return: false,
    };

    /// Every normally reaching path through this statement sequence returns.
    ///
    /// Dynamic traps are outside this structural fact: they terminate without
    /// cleanup rather than becoming a return edge.
    pub(crate) const fn definitely_returns(self) -> bool {
        self.has_reachable_return && !self.reaches_next
    }

    pub(crate) const fn can_fall_through(self) -> bool {
        self.reaches_next
    }

    #[cfg(test)]
    pub(crate) const fn has_reachable_return(self) -> bool {
        self.has_reachable_return
    }

    /// A return occurs anywhere in the syntax tree, including below a branch
    /// that is unreachable in a forged AST. Lexical exposure uses this stricter
    /// fact because `return` is forbidden in its body, not merely on paths that
    /// happen to reach its closing brace.
    pub(crate) const fn contains_return(self) -> bool {
        self.contains_return
    }
}

#[cfg(test)]
pub(crate) fn summarize_block(statements: &[Stmt]) -> FlowSummary {
    let mut summary = FlowSummary::FALLTHROUGH;

    for statement in statements {
        let statement = summarize_statement(statement);
        summary.contains_return |= statement.contains_return;
        if summary.reaches_next {
            summary.has_reachable_return |= statement.has_reachable_return;
            summary.reaches_next = statement.reaches_next;
        }
    }

    summary
}

#[cfg(test)]
fn summarize_statement(statement: &Stmt) -> FlowSummary {
    match statement {
        Stmt::Return { .. } => FlowSummary {
            reaches_next: false,
            has_reachable_return: true,
            contains_return: true,
        },
        Stmt::If {
            then_block,
            else_block,
            ..
        } => {
            let then_flow = summarize_block(then_block);
            let else_flow = else_block
                .as_deref()
                .map_or(FlowSummary::FALLTHROUGH, summarize_block);
            FlowSummary {
                reaches_next: then_flow.reaches_next || else_flow.reaches_next,
                has_reachable_return: then_flow.has_reachable_return
                    || else_flow.has_reachable_return,
                contains_return: then_flow.contains_return || else_flow.contains_return,
            }
        }
        Stmt::While { body, .. } => {
            let body = summarize_block(body);
            FlowSummary {
                // The condition may be false before the first iteration.
                reaches_next: true,
                has_reachable_return: body.has_reachable_return,
                contains_return: body.contains_return,
            }
        }
        Stmt::Unsafe { body, .. } | Stmt::Expose { body, .. } => summarize_block(body),
        Stmt::Decl { .. }
        | Stmt::Assign { .. }
        | Stmt::ExprStmt(_)
        | Stmt::Assert(_)
        | Stmt::VarDecl { .. }
        | Stmt::FieldAssign { .. }
        | Stmt::FieldStore { .. }
        | Stmt::Store { .. }
        | Stmt::StaticAlloc { .. }
        | Stmt::SystemAlloc { .. }
        | Stmt::SystemDealloc { .. } => FlowSummary::FALLTHROUGH,
    }
}

/// A lexical scope identity. IDs are meaningful only inside their owning
/// [`BodyPlan`]; stable lookup uses [`ScopeKey`], never traversal order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ScopeId(usize);

/// A candidate runtime drop identity. Whether its declaration/initialization
/// has made the place safely droppable, and whether a later move left it
/// empty, remain dynamic consumer decisions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct DropId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BranchArm {
    Then,
    Else,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ScopeKind {
    Frame,
    Body,
    BranchArm(BranchArm),
    LoopBody,
    Exposure,
}

/// Structural block identity, distinct from lexical scope identity.
///
/// In particular, an `unsafe` block has a [`BlockId`] while sharing its
/// parent's [`ScopeId`]. IDs are retained from the pre-check outline into the
/// typed body plan; stable external lookup still uses typed site keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BlockId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BranchId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct LoopId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ExposureId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BlockKind {
    Body,
    BranchArm(BranchArm),
    LoopBody,
    Unsafe,
    Exposure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LinearStatementKind {
    Decl,
    Assign,
    Expr,
    Assert,
    VarDecl,
    FieldAssign,
    FieldStore,
    Store,
    StaticAlloc,
    SystemAlloc,
    SystemDealloc,
}

/// The structural control role of one statement in a retained block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StatementPlanKind {
    Linear(LinearStatementKind),
    Return,
    Branch(BranchId),
    Loop(LoopId),
    Unsafe(BlockId),
    Exposure(ExposureId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StatementPlan {
    entry_reachable: bool,
    flow: FlowSummary,
    kind: StatementPlanKind,
}

impl StatementPlan {
    pub(crate) const fn entry_reachable(&self) -> bool {
        self.entry_reachable
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }

    pub(crate) const fn kind(&self) -> StatementPlanKind {
        self.kind
    }
}

/// One retained source block. A block is structural even when it introduces
/// no lexical lifetime (`unsafe`); `scope` is therefore not necessarily unique
/// to the block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BlockPlan {
    id: BlockId,
    parent: Option<BlockId>,
    scope: ScopeId,
    kind: BlockKind,
    anchor: Span,
    flow: FlowSummary,
    statements: Vec<StatementPlan>,
}

impl BlockPlan {
    pub(crate) const fn id(&self) -> BlockId {
        self.id
    }

    pub(crate) const fn parent(&self) -> Option<BlockId> {
        self.parent
    }

    pub(crate) const fn scope(&self) -> ScopeId {
        self.scope
    }

    pub(crate) const fn kind(&self) -> BlockKind {
        self.kind
    }

    pub(crate) const fn anchor(&self) -> Span {
        self.anchor
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }

    pub(crate) fn statements(&self) -> &[StatementPlan] {
        &self.statements
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OutlineScope {
    parent: Option<ScopeId>,
    kind: ScopeKind,
    anchor: Span,
}

/// Pre-check branch structure. Cleanup-bearing normal edges are sealed into
/// [`BranchPlan`] only after source checking has annotated every type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BranchOutline {
    id: BranchId,
    parent_scope: ScopeId,
    anchor: Span,
    then_block: BlockId,
    else_block: Option<BlockId>,
    flow: FlowSummary,
}

impl BranchOutline {
    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }

    pub(crate) const fn anchor(&self) -> Span {
        self.anchor
    }

    pub(crate) const fn then_block(&self) -> BlockId {
        self.then_block
    }

    pub(crate) const fn else_block(&self) -> Option<BlockId> {
        self.else_block
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LoopOutline {
    id: LoopId,
    parent_scope: ScopeId,
    keyword_span: Span,
    condition_span: Span,
    body: BlockId,
    flow: FlowSummary,
}

impl LoopOutline {
    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }

    pub(crate) const fn keyword_span(&self) -> Span {
        self.keyword_span
    }

    pub(crate) const fn condition_span(&self) -> Span {
        self.condition_span
    }

    pub(crate) const fn body(&self) -> BlockId {
        self.body
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExposureOutline {
    id: ExposureId,
    parent_scope: ScopeId,
    keyword_span: Span,
    body: BlockId,
    flow: FlowSummary,
}

impl ExposureOutline {
    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }

    pub(crate) const fn keyword_span(&self) -> Span {
        self.keyword_span
    }

    pub(crate) const fn body(&self) -> BlockId {
        self.body
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }
}

/// Total structural plan built before body typechecking.
///
/// Construction deliberately has no failure path. Parser/type/checker
/// diagnostics therefore remain authoritative even for a forged tree with
/// duplicate spans. Stable-key ambiguity is rejected later, when the checked
/// outline is sealed into [`BodyPlan`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ControlOutline {
    owner: CallOwner,
    declaration_span: Span,
    scopes: Vec<OutlineScope>,
    blocks: Vec<BlockPlan>,
    branches: Vec<BranchOutline>,
    loops: Vec<LoopOutline>,
    exposures: Vec<ExposureOutline>,
    frame_scope: ScopeId,
    body_scope: ScopeId,
    body_block: BlockId,
}

impl ControlOutline {
    pub(crate) fn build(owner: CallOwner, declaration_span: Span, body: &[Stmt]) -> Self {
        let mut builder = OutlineBuilder {
            outline: Self {
                owner,
                declaration_span,
                scopes: Vec::new(),
                blocks: Vec::new(),
                branches: Vec::new(),
                loops: Vec::new(),
                exposures: Vec::new(),
                frame_scope: ScopeId(0),
                body_scope: ScopeId(0),
                body_block: BlockId(0),
            },
        };
        let frame_scope = builder.add_scope(ScopeKind::Frame, declaration_span, None);
        let body_scope = builder.add_scope(ScopeKind::Body, declaration_span, Some(frame_scope));
        let body_block =
            builder.build_block(body, BlockKind::Body, declaration_span, None, body_scope);
        builder.outline.frame_scope = frame_scope;
        builder.outline.body_scope = body_scope;
        builder.outline.body_block = body_block;
        builder.outline
    }

    pub(crate) fn owner(&self) -> &CallOwner {
        &self.owner
    }

    pub(crate) const fn declaration_span(&self) -> Span {
        self.declaration_span
    }

    pub(crate) const fn frame_scope(&self) -> ScopeId {
        self.frame_scope
    }

    pub(crate) const fn body_scope(&self) -> ScopeId {
        self.body_scope
    }

    pub(crate) const fn body_block(&self) -> BlockId {
        self.body_block
    }

    pub(crate) fn block(&self, id: BlockId) -> &BlockPlan {
        &self.blocks[id.0]
    }

    pub(crate) fn statement(&self, block: BlockId, index: usize) -> &StatementPlan {
        &self.block(block).statements[index]
    }

    pub(crate) fn branch(&self, id: BranchId) -> &BranchOutline {
        &self.branches[id.0]
    }

    pub(crate) fn loop_plan(&self, id: LoopId) -> &LoopOutline {
        &self.loops[id.0]
    }

    pub(crate) fn exposure(&self, id: ExposureId) -> &ExposureOutline {
        &self.exposures[id.0]
    }

    fn structurally_matches(&self, body: &[Stmt]) -> bool {
        Self::build(self.owner.clone(), self.declaration_span, body) == *self
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ControlOutlines {
    bodies: Vec<ControlOutline>,
}

impl ControlOutlines {
    pub(crate) fn push(&mut self, outline: ControlOutline) {
        self.bodies.push(outline);
    }

    fn for_program(program: &Program) -> Self {
        let mut outlines = Self::default();
        for function in &program.fns {
            if function.extern_info.is_none() {
                outlines.push(ControlOutline::build(
                    CallOwner::Function(function.name.clone()),
                    function.span,
                    &function.body,
                ));
            }
        }
        for function in &program.fn_templates {
            outlines.push(ControlOutline::build(
                CallOwner::Function(function.name.clone()),
                function.span,
                &function.body,
            ));
        }
        for class in program.classes.iter().chain(&program.class_templates) {
            for initializer in &class.inits {
                outlines.push(ControlOutline::build(
                    CallOwner::Constructor {
                        class: class.name.clone(),
                        init: initializer.name.clone(),
                    },
                    initializer.span,
                    &initializer.body,
                ));
            }
            for method in &class.methods {
                outlines.push(ControlOutline::build(
                    CallOwner::Method {
                        class: class.name.clone(),
                        method: method.f.name.clone(),
                    },
                    method.f.span,
                    &method.f.body,
                ));
            }
            if let Some(body) = &class.deinit {
                outlines.push(ControlOutline::build(
                    CallOwner::Deinitializer {
                        class: class.name.clone(),
                    },
                    class.span,
                    body,
                ));
            }
        }
        outlines
    }

    fn exact(
        &self,
        owner: &CallOwner,
        declaration_span: Span,
    ) -> Result<&ControlOutline, PlanError> {
        let mut matches = self.bodies.iter().filter(|outline| {
            outline.owner() == owner && outline.declaration_span() == declaration_span
        });
        let Some(outline) = matches.next() else {
            return Err(PlanError {
                span: declaration_span,
                message: format!("control outlines have no body for {}", owner.render()),
            });
        };
        if matches.next().is_some() {
            return Err(PlanError {
                span: declaration_span,
                message: format!("duplicate control outline identity for {}", owner.render()),
            });
        }
        Ok(outline)
    }
}

struct OutlineBuilder {
    outline: ControlOutline,
}

impl OutlineBuilder {
    fn add_scope(&mut self, kind: ScopeKind, anchor: Span, parent: Option<ScopeId>) -> ScopeId {
        let id = ScopeId(self.outline.scopes.len());
        self.outline.scopes.push(OutlineScope {
            parent,
            kind,
            anchor,
        });
        id
    }

    fn reserve_block(
        &mut self,
        kind: BlockKind,
        anchor: Span,
        parent: Option<BlockId>,
        scope: ScopeId,
    ) -> BlockId {
        let id = BlockId(self.outline.blocks.len());
        self.outline.blocks.push(BlockPlan {
            id,
            parent,
            scope,
            kind,
            anchor,
            flow: FlowSummary::FALLTHROUGH,
            statements: Vec::new(),
        });
        id
    }

    fn build_block(
        &mut self,
        statements: &[Stmt],
        kind: BlockKind,
        anchor: Span,
        parent: Option<BlockId>,
        scope: ScopeId,
    ) -> BlockId {
        let block = self.reserve_block(kind, anchor, parent, scope);
        let mut flow = FlowSummary::FALLTHROUGH;
        let mut plans = Vec::with_capacity(statements.len());
        for statement in statements {
            let statement_flow = self.build_statement(statement, block, scope);
            let entry_reachable = flow.reaches_next;
            flow.contains_return |= statement_flow.flow.contains_return;
            if entry_reachable {
                flow.has_reachable_return |= statement_flow.flow.has_reachable_return;
                flow.reaches_next = statement_flow.flow.reaches_next;
            }
            plans.push(StatementPlan {
                entry_reachable,
                flow: statement_flow.flow,
                kind: statement_flow.kind,
            });
        }
        self.outline.blocks[block.0].flow = flow;
        self.outline.blocks[block.0].statements = plans;
        block
    }

    fn build_statement(
        &mut self,
        statement: &Stmt,
        parent: BlockId,
        scope: ScopeId,
    ) -> StatementPlan {
        match statement {
            Stmt::Return { .. } => StatementPlan {
                entry_reachable: true,
                flow: FlowSummary {
                    reaches_next: false,
                    has_reachable_return: true,
                    contains_return: true,
                },
                kind: StatementPlanKind::Return,
            },
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let then_scope = self.add_scope(
                    ScopeKind::BranchArm(BranchArm::Then),
                    cond.span,
                    Some(scope),
                );
                let then_block = self.build_block(
                    then_block,
                    BlockKind::BranchArm(BranchArm::Then),
                    cond.span,
                    Some(parent),
                    then_scope,
                );
                let else_block = else_block.as_deref().map(|statements| {
                    let else_scope = self.add_scope(
                        ScopeKind::BranchArm(BranchArm::Else),
                        cond.span,
                        Some(scope),
                    );
                    self.build_block(
                        statements,
                        BlockKind::BranchArm(BranchArm::Else),
                        cond.span,
                        Some(parent),
                        else_scope,
                    )
                });
                let then_flow = self.outline.blocks[then_block.0].flow;
                let else_flow = else_block
                    .map(|block| self.outline.blocks[block.0].flow)
                    .unwrap_or(FlowSummary::FALLTHROUGH);
                let flow = FlowSummary {
                    reaches_next: then_flow.reaches_next || else_flow.reaches_next,
                    has_reachable_return: then_flow.has_reachable_return
                        || else_flow.has_reachable_return,
                    contains_return: then_flow.contains_return || else_flow.contains_return,
                };
                let id = BranchId(self.outline.branches.len());
                self.outline.branches.push(BranchOutline {
                    id,
                    parent_scope: scope,
                    anchor: cond.span,
                    then_block,
                    else_block,
                    flow,
                });
                StatementPlan {
                    entry_reachable: true,
                    flow,
                    kind: StatementPlanKind::Branch(id),
                }
            }
            Stmt::While {
                cond,
                kw_span,
                body,
                ..
            } => {
                let body_scope = self.add_scope(ScopeKind::LoopBody, *kw_span, Some(scope));
                let body = self.build_block(
                    body,
                    BlockKind::LoopBody,
                    *kw_span,
                    Some(parent),
                    body_scope,
                );
                let body_flow = self.outline.blocks[body.0].flow;
                let flow = FlowSummary {
                    reaches_next: true,
                    has_reachable_return: body_flow.has_reachable_return,
                    contains_return: body_flow.contains_return,
                };
                let id = LoopId(self.outline.loops.len());
                self.outline.loops.push(LoopOutline {
                    id,
                    parent_scope: scope,
                    keyword_span: *kw_span,
                    condition_span: cond.span,
                    body,
                    flow,
                });
                StatementPlan {
                    entry_reachable: true,
                    flow,
                    kind: StatementPlanKind::Loop(id),
                }
            }
            Stmt::Unsafe { kw_span, body, .. } => {
                let body = self.build_block(body, BlockKind::Unsafe, *kw_span, Some(parent), scope);
                StatementPlan {
                    entry_reachable: true,
                    flow: self.outline.blocks[body.0].flow,
                    kind: StatementPlanKind::Unsafe(body),
                }
            }
            Stmt::Expose { kw_span, body, .. } => {
                let body_scope = self.add_scope(ScopeKind::Exposure, *kw_span, Some(scope));
                let body = self.build_block(
                    body,
                    BlockKind::Exposure,
                    *kw_span,
                    Some(parent),
                    body_scope,
                );
                let flow = self.outline.blocks[body.0].flow;
                let id = ExposureId(self.outline.exposures.len());
                self.outline.exposures.push(ExposureOutline {
                    id,
                    parent_scope: scope,
                    keyword_span: *kw_span,
                    body,
                    flow,
                });
                StatementPlan {
                    entry_reachable: true,
                    flow,
                    kind: StatementPlanKind::Exposure(id),
                }
            }
            Stmt::Decl { .. } => Self::linear(LinearStatementKind::Decl),
            Stmt::Assign { .. } => Self::linear(LinearStatementKind::Assign),
            Stmt::ExprStmt(_) => Self::linear(LinearStatementKind::Expr),
            Stmt::Assert(_) => Self::linear(LinearStatementKind::Assert),
            Stmt::VarDecl { .. } => Self::linear(LinearStatementKind::VarDecl),
            Stmt::FieldAssign { .. } => Self::linear(LinearStatementKind::FieldAssign),
            Stmt::FieldStore { .. } => Self::linear(LinearStatementKind::FieldStore),
            Stmt::Store { .. } => Self::linear(LinearStatementKind::Store),
            Stmt::StaticAlloc { .. } => Self::linear(LinearStatementKind::StaticAlloc),
            Stmt::SystemAlloc { .. } => Self::linear(LinearStatementKind::SystemAlloc),
            Stmt::SystemDealloc { .. } => Self::linear(LinearStatementKind::SystemDealloc),
        }
    }

    fn linear(kind: LinearStatementKind) -> StatementPlan {
        StatementPlan {
            entry_reachable: true,
            flow: FlowSummary::FALLTHROUGH,
            kind: StatementPlanKind::Linear(kind),
        }
    }
}

/// Stable structural identity for a cleanup scope.
///
/// `anchor` is the owning function span for frame/body scopes, the condition
/// span for an `if` arm, and the keyword span for a loop or exposure. `unsafe`
/// is intentionally absent: it is a capability marker, not a lifetime.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ScopeKey {
    owner: CallOwner,
    kind: ScopeKind,
    anchor: Span,
}

impl ScopeKey {
    fn new(owner: &CallOwner, kind: ScopeKind, anchor: Span) -> Self {
        Self {
            owner: owner.clone(),
            kind,
            anchor,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct DropCandidate {
    id: DropId,
    scope: ScopeId,
    place: Place,
    drop_action: ValueDropAction,
    span: Span,
}

impl DropCandidate {
    pub(crate) const fn id(&self) -> DropId {
        self.id
    }

    pub(crate) const fn scope(&self) -> ScopeId {
        self.scope
    }

    pub(crate) fn place(&self) -> &Place {
        &self.place
    }

    pub(crate) fn ty(&self) -> &Ty {
        self.drop_action.ty()
    }

    pub(crate) fn drop_action(&self) -> &ValueDropAction {
        &self.drop_action
    }

    pub(crate) const fn span(&self) -> Span {
        self.span
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExitKind {
    Fallthrough,
    Return,
    Backedge,
    ExposureClose,
    Trap,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CompilerTempKind {
    ReturnValue,
    AssignmentValue,
    FieldAssignmentValue,
    DiscardedClassValue,
    ExposureLoan,
    ExposureIndex,
    ExposureByte,
    BoolLiteralElement(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct CompilerTempKey {
    scope: ScopeId,
    anchor: Span,
    kind: CompilerTempKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct AssignmentKey {
    scope: ScopeId,
    span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FieldAssignmentKey {
    scope: ScopeId,
    span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TemporaryDropKey {
    scope: ScopeId,
    span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct BranchKey {
    parent_scope: ScopeId,
    anchor: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct LoopKey {
    parent_scope: ScopeId,
    keyword_span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ExposureKey {
    parent_scope: ScopeId,
    keyword_span: Span,
}

/// How an assignment keeps the fully evaluated RHS alive while replacing its
/// destination. Cleanup-bearing values require a distinct temporary identity;
/// direct values may remain in a consumer's ordinary expression result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AssignmentStaging {
    Direct,
    Temporary(Place),
}

/// Exact link from a statement cleanup action to the concrete class recipe in
/// [`ControlProgram`]. The index selects one [`ClassDropPlan`]; the terminal
/// route is repeated here so the statement sequence itself cannot silently
/// acquire unwinding behavior.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClassDropAction {
    class: usize,
    terminal_trap: ExitRoute,
}

/// The exact recursive recipe for destroying one cleanup-bearing value.
///
/// This is deliberately narrower than [`Ty::is_affine`]. Resources carry an
/// explicit must-consume authority and never acquire implicit destruction.
/// Arrays currently release one total, initialized buffer whose elements are
/// non-affine; admitting affine elements requires a separate occupied-slot
/// model and is rejected here rather than silently compiling as a raw free.
/// An owning option destroys only its dynamically present payload, using the
/// payload's retained action rather than rediscovering that recipe at use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ValueDropAction {
    ty: Ty,
    recipe: ValueDropRecipe,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ValueDropRecipe {
    ReleaseArray { element: Ty },
    DropClass(ClassDropAction),
    DropPresent(Box<ValueDropAction>),
}

impl ValueDropAction {
    fn build(ty: &Ty, span: Span) -> Result<Option<Self>, PlanError> {
        let recipe = match ty {
            Ty::Class(class) => ValueDropRecipe::DropClass(ClassDropAction::new(*class)),
            Ty::Array(element) if element.is_affine() => {
                return Err(PlanError {
                    span,
                    message: format!(
                        "owned array `{}` has no sealed occupied-slot cleanup recipe",
                        ty.name()
                    ),
                });
            }
            Ty::Array(element) => ValueDropRecipe::ReleaseArray {
                element: element.as_ref().clone(),
            },
            Ty::Slots(_) => {
                return Err(PlanError {
                    span,
                    message: format!(
                        "internal.control.slots_unsupported: `{}` has no sealed occupied-cell cleanup recipe",
                        ty.name()
                    ),
                });
            }
            Ty::Option(payload) if payload.as_owned_slots().is_some() => {
                return Err(PlanError {
                    span,
                    message: format!(
                        "internal.control.slots_unsupported: owning option `{}` has no present-slot cleanup recipe",
                        ty.name()
                    ),
                });
            }
            Ty::Option(payload) if !payload.is_affine() => return Ok(None),
            Ty::Option(payload)
                if payload.is_owned_array_of(&Ty::Bool)
                    || matches!(payload.as_ref(), Ty::Class(_)) =>
            {
                let payload_action = Self::build(payload, span)?.ok_or_else(|| PlanError {
                    span,
                    message: format!(
                        "owning option `{}` lost its present-payload cleanup recipe",
                        ty.name()
                    ),
                })?;
                ValueDropRecipe::DropPresent(Box::new(payload_action))
            }
            Ty::Option(_) => {
                return Err(PlanError {
                    span,
                    message: format!(
                        "owning option `{}` is outside the sealed one-level cleanup family",
                        ty.name()
                    ),
                });
            }
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Borrow(..)
            | Ty::Unit => return Ok(None),
        };
        Ok(Some(Self {
            ty: ty.clone(),
            recipe,
        }))
    }

    pub(crate) fn ty(&self) -> &Ty {
        &self.ty
    }

    pub(crate) fn recipe(&self) -> &ValueDropRecipe {
        &self.recipe
    }
}

impl ClassDropAction {
    fn new(class: usize) -> Self {
        Self {
            class,
            terminal_trap: ExitRoute::terminal_trap(),
        }
    }

    pub(crate) const fn class(&self) -> usize {
        self.class
    }

    pub(crate) fn terminal_trap_route(&self) -> &ExitRoute {
        &self.terminal_trap
    }
}

/// One checker-sealed local replacement action.
///
/// Consumers may choose their own concrete value representation, but not
/// rediscover the destination, the old cleanup candidate, or whether the RHS
/// must survive in temporary storage. The semantic order is always evaluate
/// into `staging`, drop `previous` if dynamically live, then install into
/// `destination`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AssignmentAction {
    scope: ScopeId,
    span: Span,
    destination: Place,
    ty: Ty,
    transfer_key: ValueTransferKey,
    previous: Option<DropId>,
    staging: AssignmentStaging,
}

/// One checker-sealed `self.field = value` action.
///
/// This has one rule for constructors and methods alike: evaluate the RHS into
/// `staging`, conditionally destroy the destination when `drop_if_present` and
/// dynamically live, then install. A constructor's first write is therefore
/// not a second static policy; its consumer simply observes an absent field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FieldAssignmentAction {
    scope: ScopeId,
    span: Span,
    destination: Place,
    ty: Ty,
    transfer_key: ValueTransferKey,
    staging: AssignmentStaging,
    drop_action: Option<ValueDropAction>,
}

/// One discarded fresh class result and its mandatory statement-end drop.
/// The temporary is compiler-owned, never a lexical binding. Evaluation and
/// every class-drop phase precede the following statement; a failure takes the
/// retained terminal no-unwind route and skips that continuation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TemporaryDropAction {
    scope: ScopeId,
    span: Span,
    transfer_key: ValueTransferKey,
    temporary: Place,
    drop_action: ValueDropAction,
}

/// The two distinct failure edges of a native owned-array allocation.
///
/// A requested logical length above the language cap is different from a
/// conforming allocator returning null for an otherwise admitted request.
/// Keeping both identities prevents a backend from silently collapsing one
/// of the required guards into a body-level "may trap" bit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum AllocationTrapPhase {
    Capacity,
    Allocator,
}

/// Stable semantic shape of one source-level trap edge.
///
/// Names, checked integer/payload types, and clause text participate wherever
/// changing them would change the operation. Together with lexical scope and
/// source span this is an injective structural key; two cloned/desugared sites
/// with the same key are refused rather than assigned traversal ordinals.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TrapSiteKind {
    AddOverflow(IntTy),
    SubOverflow(IntTy),
    MulOverflow(IntTy),
    NegOverflow(IntTy),
    DivByZero(IntTy),
    RemByZero(IntTy),
    DivOverflow(IntTy),
    NarrowRange {
        source: IntTy,
        target: IntTy,
    },
    OptionValue(Ty),
    OptionTake {
        option: String,
        payload: Ty,
    },
    ArrayAllocation {
        element: Ty,
        phase: AllocationTrapPhase,
    },
    ArrayIndex {
        array: String,
        element: Ty,
    },
    SelfFieldIndex {
        field: String,
        element: Ty,
    },
    ClassFieldIndex {
        object: String,
        field: String,
        element: Ty,
    },
    FunctionCall {
        callee: String,
        result: Ty,
    },
    ConstructorCall {
        class: String,
        initializer: String,
        result: Ty,
    },
    MethodCall {
        receiver: String,
        method: String,
        result: Ty,
    },
    RawOperation(String),
    ResourceOperation(String),
    DeviceOperation(String),
    ArrayStore {
        array: String,
        element: Ty,
    },
    SelfFieldStore {
        field: String,
        element: Ty,
    },
    SystemDealloc,
    ExposureClose {
        array: String,
        mutable: bool,
    },
    InlineAssert(String),
    LoopInvariant(String),
    LoopVariantNegative(String),
    LoopVariantNonDecrease(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct TrapSiteKey {
    scope: ScopeId,
    span: Span,
    kind: TrapSiteKind,
}

/// One checker-sealed source trap edge and its canonical no-unwind route.
///
/// Consumers inspect the retained site immediately before executing or
/// lowering the corresponding operation. The route is deliberately empty:
/// Sable traps abort and do not run lexical cleanup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TrapSite {
    key: TrapSiteKey,
    route: ExitRoute,
}

impl TrapSite {
    pub(crate) const fn scope(&self) -> ScopeId {
        self.key.scope
    }

    pub(crate) const fn span(&self) -> Span {
        self.key.span
    }

    pub(crate) fn route(&self) -> &ExitRoute {
        &self.route
    }
}

impl AssignmentAction {
    pub(crate) const fn scope(&self) -> ScopeId {
        self.scope
    }

    pub(crate) const fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn destination(&self) -> &Place {
        &self.destination
    }

    pub(crate) fn ty(&self) -> &Ty {
        &self.ty
    }

    pub(crate) fn transfer_key(&self) -> &ValueTransferKey {
        &self.transfer_key
    }

    pub(crate) const fn previous(&self) -> Option<DropId> {
        self.previous
    }

    pub(crate) fn staging(&self) -> &AssignmentStaging {
        &self.staging
    }
}

impl FieldAssignmentAction {
    pub(crate) const fn scope(&self) -> ScopeId {
        self.scope
    }

    pub(crate) const fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn destination(&self) -> &Place {
        &self.destination
    }

    pub(crate) fn ty(&self) -> &Ty {
        &self.ty
    }

    pub(crate) fn transfer_key(&self) -> &ValueTransferKey {
        &self.transfer_key
    }

    pub(crate) const fn drop_if_present(&self) -> bool {
        self.drop_action.is_some()
    }

    pub(crate) fn staging(&self) -> &AssignmentStaging {
        &self.staging
    }

    pub(crate) fn drop_action(&self) -> Option<&ValueDropAction> {
        self.drop_action.as_ref()
    }
}

impl TemporaryDropAction {
    pub(crate) const fn scope(&self) -> ScopeId {
        self.scope
    }

    pub(crate) const fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn ty(&self) -> &Ty {
        self.drop_action.ty()
    }

    pub(crate) fn transfer_key(&self) -> &ValueTransferKey {
        &self.transfer_key
    }

    pub(crate) fn temporary(&self) -> &Place {
        &self.temporary
    }

    pub(crate) fn drop_action(&self) -> &ValueDropAction {
        &self.drop_action
    }
}

/// One normalized lexical exit route. Scopes and candidates are ordered in
/// execution order: innermost scope first, each scope's candidates in reverse
/// declaration order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExitRoute {
    kind: ExitKind,
    scopes: Vec<ScopeId>,
    /// Every lexical binding whose lifetime ends on this edge, in reverse
    /// declaration order within each inner-to-outer scope. Runtime drop
    /// candidates are a typed subset of these places.
    clears: Vec<Place>,
    drops: Vec<DropId>,
}

impl ExitRoute {
    fn terminal_trap() -> Self {
        Self {
            kind: ExitKind::Trap,
            scopes: Vec::new(),
            clears: Vec::new(),
            drops: Vec::new(),
        }
    }

    fn is_terminal_trap(&self) -> bool {
        self.kind == ExitKind::Trap
            && self.scopes.is_empty()
            && self.clears.is_empty()
            && self.drops.is_empty()
    }

    pub(crate) const fn kind(&self) -> ExitKind {
        self.kind
    }

    pub(crate) fn scopes(&self) -> &[ScopeId] {
        &self.scopes
    }

    pub(crate) fn clears(&self) -> &[Place] {
        &self.clears
    }

    pub(crate) fn drops(&self) -> &[DropId] {
        &self.drops
    }
}

/// A return has two cleanup phases in the dynamic monitor: lexical locals die
/// before postconditions are checked, while owned parameters remain available
/// to those postconditions and die with the frame afterward. A backend that
/// erases contracts may emit the two routes consecutively. The formal SVM is
/// the exception: its `ret`/`retUnit` step restores outstanding loans from the
/// parameter frame and then discards that frame, so it consumes the frame
/// route by that fused return operation rather than clearing parameters first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnRoutes {
    lexical: ExitRoute,
    frame: ExitRoute,
    /// Compiler-only storage that receives an explicit result before the
    /// lexical route runs. It belongs to no source scope, so clearing the
    /// returned local cannot erase the value in flight. Implicit unit returns
    /// do not need a slot.
    result_slot: Option<Place>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BranchArmPlan {
    block: BlockId,
    scope: ScopeId,
    flow: FlowSummary,
    /// Present exactly when this arm has a normally reaching edge to the
    /// parent's continuation.
    normal_exit: Option<ExitRoute>,
}

impl BranchArmPlan {
    pub(crate) const fn block(&self) -> BlockId {
        self.block
    }

    pub(crate) const fn scope(&self) -> ScopeId {
        self.scope
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }

    pub(crate) fn normal_exit(&self) -> Option<&ExitRoute> {
        self.normal_exit.as_ref()
    }
}

/// Checker-sealed structured branch edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BranchPlan {
    id: BranchId,
    parent_scope: ScopeId,
    anchor: Span,
    then_arm: BranchArmPlan,
    else_arm: Option<BranchArmPlan>,
    flow: FlowSummary,
}

impl BranchPlan {
    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }

    pub(crate) const fn anchor(&self) -> Span {
        self.anchor
    }

    pub(crate) fn then_arm(&self) -> &BranchArmPlan {
        &self.then_arm
    }

    pub(crate) fn else_arm(&self) -> Option<&BranchArmPlan> {
        self.else_arm.as_ref()
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }
}

/// Checker-sealed loop header/body/backedge structure. Proof-specific havoc
/// is linked by `effect_key`; consumers may not rediscover a different loop
/// effect site from statement syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LoopPlan {
    id: LoopId,
    parent_scope: ScopeId,
    keyword_span: Span,
    condition_span: Span,
    body: BlockId,
    body_scope: ScopeId,
    body_flow: FlowSummary,
    backedge: Option<ExitRoute>,
    effect_key: EffectSiteKey,
    flow: FlowSummary,
}

impl LoopPlan {
    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }

    pub(crate) const fn keyword_span(&self) -> Span {
        self.keyword_span
    }

    pub(crate) const fn condition_span(&self) -> Span {
        self.condition_span
    }

    pub(crate) const fn body(&self) -> BlockId {
        self.body
    }

    pub(crate) const fn body_scope(&self) -> ScopeId {
        self.body_scope
    }

    pub(crate) const fn body_flow(&self) -> FlowSummary {
        self.body_flow
    }

    pub(crate) fn backedge(&self) -> Option<&ExitRoute> {
        self.backedge.as_ref()
    }

    pub(crate) fn effect_key(&self) -> &EffectSiteKey {
        &self.effect_key
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExposureRebuildAction {
    owner: Place,
    owner_span: Span,
    owner_ty: Ty,
    mutability: Mutability,
    pointer: Place,
    resource: Place,
    keyword_span: Span,
}

impl ExposureRebuildAction {
    pub(crate) fn owner(&self) -> &Place {
        &self.owner
    }

    pub(crate) const fn owner_span(&self) -> Span {
        self.owner_span
    }

    pub(crate) fn owner_ty(&self) -> &Ty {
        &self.owner_ty
    }

    pub(crate) const fn mutability(&self) -> Mutability {
        self.mutability
    }

    pub(crate) fn pointer(&self) -> &Place {
        &self.pointer
    }

    pub(crate) fn resource(&self) -> &Place {
        &self.resource
    }

    pub(crate) const fn keyword_span(&self) -> Span {
        self.keyword_span
    }
}

/// Normal exposure close, in semantic execution order: capture the final
/// resource view/bytes, end the body bindings, rebuild/copy back the owner,
/// release the raw loan, then close compiler scratch before continuing in the
/// parent scope. The concrete capture/release representation is consumer
/// state; their identities and order are not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExposureNormalPlan {
    capture: Place,
    body_exit: ExitRoute,
    rebuild: ExposureRebuildAction,
    release_loan: Place,
    close: ExitRoute,
    parent_scope: ScopeId,
}

impl ExposureNormalPlan {
    pub(crate) fn capture(&self) -> &Place {
        &self.capture
    }

    pub(crate) fn body_exit(&self) -> &ExitRoute {
        &self.body_exit
    }

    pub(crate) fn rebuild(&self) -> &ExposureRebuildAction {
        &self.rebuild
    }

    pub(crate) fn release_loan(&self) -> &Place {
        &self.release_loan
    }

    pub(crate) fn close(&self) -> &ExitRoute {
        &self.close
    }

    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExposurePlan {
    id: ExposureId,
    parent_scope: ScopeId,
    keyword_span: Span,
    body: BlockId,
    body_scope: ScopeId,
    body_flow: FlowSummary,
    effect_key: EffectSiteKey,
    normal: Option<ExposureNormalPlan>,
    flow: FlowSummary,
}

impl ExposurePlan {
    pub(crate) const fn parent_scope(&self) -> ScopeId {
        self.parent_scope
    }

    pub(crate) const fn keyword_span(&self) -> Span {
        self.keyword_span
    }

    pub(crate) const fn body(&self) -> BlockId {
        self.body
    }

    pub(crate) const fn body_scope(&self) -> ScopeId {
        self.body_scope
    }

    pub(crate) const fn body_flow(&self) -> FlowSummary {
        self.body_flow
    }

    pub(crate) fn effect_key(&self) -> &EffectSiteKey {
        &self.effect_key
    }

    pub(crate) fn normal(&self) -> Option<&ExposureNormalPlan> {
        self.normal.as_ref()
    }

    pub(crate) const fn flow(&self) -> FlowSummary {
        self.flow
    }
}

/// Exact declaration identity retained for one class invariant. The dynamic
/// monitor evaluates the clauses in the class declaration, while this shape
/// prevents a mutated post-check AST from substituting a different contract
/// under an already-authorized destruction recipe.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClassInvariantShape {
    kind: ClauseKind,
    label: Option<String>,
    fact: bool,
    unfold: bool,
    text: String,
    span: Span,
    line_span: Span,
}

impl From<&Clause> for ClassInvariantShape {
    fn from(clause: &Clause) -> Self {
        Self {
            kind: clause.kind,
            label: clause.label.clone(),
            fact: clause.fact,
            unfold: clause.unfold,
            text: clause.text.clone(),
            span: clause.span,
            line_span: clause.line_span,
        }
    }
}

/// One declared field in a concrete class's destruction order.
///
/// Every field is retained, including scalar fields whose current runtime
/// representation needs no destructor. That makes reverse declaration order
/// an exact semantic fact rather than a filtered backend reconstruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClassDropField {
    index: usize,
    name: String,
    ty: Ty,
    drop_action: Option<ValueDropAction>,
    span: Span,
    must_consume: bool,
}

impl ClassDropField {
    pub(crate) const fn index(&self) -> usize {
        self.index
    }

    pub(crate) fn name(&self) -> &str {
        &self.name
    }

    pub(crate) fn ty(&self) -> &Ty {
        &self.ty
    }

    pub(crate) fn drop_action(&self) -> Option<&ValueDropAction> {
        self.drop_action.as_ref()
    }

    pub(crate) const fn span(&self) -> Span {
        self.span
    }

    pub(crate) const fn must_consume(&self) -> bool {
        self.must_consume
    }
}

/// Ordered semantic phases for destroying one concrete class value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ClassDropPhase {
    CheckInvariant,
    RunDeinitializer(CallOwner),
    DropField(ClassDropField),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClassDropShape {
    name: String,
    name_span: Span,
    declaration_span: Span,
    invariants: Vec<ClassInvariantShape>,
    fields: Vec<ClassDropField>,
    has_deinitializer: bool,
}

impl ClassDropShape {
    fn from_declaration(declaration: &ClassDecl) -> Result<Self, PlanError> {
        Ok(Self {
            name: declaration.name.clone(),
            name_span: declaration.name_span,
            declaration_span: declaration.span,
            invariants: declaration
                .invariants
                .iter()
                .map(ClassInvariantShape::from)
                .collect(),
            fields: declaration
                .fields
                .iter()
                .enumerate()
                .map(|(index, field)| {
                    Ok(ClassDropField {
                        index,
                        name: field.name.clone(),
                        ty: field.ty.clone(),
                        drop_action: ValueDropAction::build(&field.ty, field.span)?,
                        span: field.span,
                        must_consume: field.must_consume,
                    })
                })
                .collect::<Result<Vec<_>, PlanError>>()?,
            has_deinitializer: declaration.deinit.is_some(),
        })
    }
}

/// Checker-retained destruction recipe for one concrete class.
///
/// A failure in any phase takes `terminal_trap`: invariant failure,
/// deinitializer failure, and a recursive field failure all abort the suffix
/// without unwinding later fields. Runtime liveness remains representation
/// state: a consumer skips a field that a deinitializer moved out, but it may
/// not rediscover phase order from the declaration.
#[derive(Clone, Debug)]
pub(crate) struct ClassDropPlan {
    class: usize,
    shape: ClassDropShape,
    phases: Vec<ClassDropPhase>,
    terminal_trap: ExitRoute,
}

impl ClassDropPlan {
    pub(crate) fn build(class: usize, declaration: &ClassDecl) -> Result<Self, PlanError> {
        let shape = ClassDropShape::from_declaration(declaration)?;
        let mut phases = vec![ClassDropPhase::CheckInvariant];
        if shape.has_deinitializer {
            phases.push(ClassDropPhase::RunDeinitializer(CallOwner::Deinitializer {
                class: shape.name.clone(),
            }));
        }
        phases.extend(
            shape
                .fields
                .iter()
                .rev()
                .cloned()
                .map(ClassDropPhase::DropField),
        );
        Ok(Self {
            class,
            shape,
            phases,
            terminal_trap: ExitRoute::terminal_trap(),
        })
    }

    pub(crate) fn validate(&self, class: usize, declaration: &ClassDecl) -> Result<(), PlanError> {
        self.validate_terminal_trap_route()?;
        let current = Self::build(class, declaration)?;
        if self.class != current.class
            || self.shape != current.shape
            || self.phases != current.phases
        {
            return Err(PlanError {
                span: declaration.name_span,
                message: format!(
                    "checked class-drop plan for concrete class `{}` no longer matches its declaration",
                    self.shape.name
                ),
            });
        }
        Ok(())
    }

    pub(crate) fn validate_terminal_trap_route(&self) -> Result<(), PlanError> {
        if !self.terminal_trap.is_terminal_trap() {
            return Err(PlanError {
                span: self.shape.declaration_span,
                message: format!(
                    "class-drop failures for `{}` no longer use the canonical no-unwind trap route",
                    self.shape.name
                ),
            });
        }
        Ok(())
    }

    pub(crate) const fn class(&self) -> usize {
        self.class
    }

    pub(crate) fn class_name(&self) -> &str {
        &self.shape.name
    }

    pub(crate) fn phases(&self) -> &[ClassDropPhase] {
        &self.phases
    }

    pub(crate) fn terminal_trap_route(&self) -> &ExitRoute {
        &self.terminal_trap
    }
}

impl ReturnRoutes {
    pub(crate) fn lexical(&self) -> &ExitRoute {
        &self.lexical
    }

    pub(crate) fn frame(&self) -> &ExitRoute {
        &self.frame
    }

    pub(crate) fn result_slot(&self) -> Option<&Place> {
        self.result_slot.as_ref()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PlanError {
    pub(crate) span: Span,
    pub(crate) message: String,
}

#[derive(Clone, Debug)]
struct Scope {
    parent: Option<ScopeId>,
    kind: ScopeKind,
    anchor: Span,
    locals: Vec<Place>,
    bindings: Vec<SourceBinding>,
    drops: Vec<DropId>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SourceBinding {
    place: Place,
    ty: Ty,
    span: Span,
}

#[derive(Default)]
struct BodyInventory {
    scopes: HashSet<ScopeId>,
    locals: HashMap<ScopeId, Vec<Place>>,
    bindings: HashMap<ScopeId, Vec<SourceBinding>>,
    assignments: HashSet<AssignmentKey>,
    field_assignments: HashSet<FieldAssignmentKey>,
    temporary_drops: HashSet<TemporaryDropKey>,
    returns: HashSet<(Span, ScopeId)>,
    compiler_temps: HashSet<CompilerTempKey>,
    traps: Vec<TrapSiteKey>,
}

/// Retained structural identities reached while reconciling a checked body.
///
/// This is deliberately separate from [`BodyInventory`]. Structural edge
/// validation runs first and follows the sealed `BlockId` graph, so the later
/// binding/drop/trap inventory never has to rediscover block parentage or
/// continuation flow from source syntax.
#[derive(Default)]
struct StructuralInventory {
    blocks: HashSet<BlockId>,
    branches: HashSet<BranchId>,
    loops: HashSet<LoopId>,
    exposures: HashSet<ExposureId>,
    scopes: HashSet<ScopeId>,
}

impl BodyInventory {
    fn source_binding(&mut self, scope: ScopeId, name: &str, ty: Ty, span: Span) {
        let place = Place::local(name);
        self.locals.entry(scope).or_default().push(place.clone());
        self.bindings
            .entry(scope)
            .or_default()
            .push(SourceBinding { place, ty, span });
    }

    fn compiler_temp(&mut self, key: CompilerTempKey, place: Place, clear_with_scope: bool) {
        if clear_with_scope {
            self.locals.entry(key.scope).or_default().push(place);
        }
        self.compiler_temps.insert(key);
    }
}

/// Typed lexical cleanup/control plan for one checked callable body.
///
/// This is deliberately not an expression CFG. It is the shared authority for
/// scope identity, conditional drop-candidate identity, local replacement
/// phases, exact source trap identity, and ordering on all structural exits.
/// Every trap site carries the explicit empty route required by Sable's
/// no-unwind semantics; fuel exhaustion, internal-plan rejection, and
/// dynamically invoked destructors are execution-engine controls rather than
/// source expression/statement trap identities.
#[derive(Clone, Debug)]
pub(crate) struct BodyPlan {
    owner: CallOwner,
    blocks: Vec<BlockPlan>,
    branches: Vec<BranchPlan>,
    branch_ids: HashMap<BranchKey, usize>,
    loops: Vec<LoopPlan>,
    loop_ids: HashMap<LoopKey, usize>,
    exposures: Vec<ExposurePlan>,
    exposure_ids: HashMap<ExposureKey, usize>,
    scopes: Vec<Scope>,
    scope_ids: HashMap<ScopeKey, ScopeId>,
    candidates: Vec<DropCandidate>,
    candidate_ids: HashMap<Place, DropId>,
    compiler_temps: HashMap<CompilerTempKey, Place>,
    assignments: Vec<AssignmentAction>,
    assignment_ids: HashMap<AssignmentKey, usize>,
    field_assignments: Vec<FieldAssignmentAction>,
    field_assignment_ids: HashMap<FieldAssignmentKey, usize>,
    temporary_drops: Vec<TemporaryDropAction>,
    temporary_drop_ids: HashMap<TemporaryDropKey, usize>,
    return_sites: HashSet<(Span, ScopeId)>,
    trap_sites: Vec<TrapSite>,
    trap_site_ids: HashMap<TrapSiteKey, usize>,
    frame_scope: ScopeId,
    body_scope: ScopeId,
    body_block: BlockId,
}

impl BodyPlan {
    pub(crate) fn build(
        owner: CallOwner,
        owner_span: Span,
        params: &[Param],
        body: &[Stmt],
    ) -> Result<Self, PlanError> {
        let outline = ControlOutline::build(owner, owner_span, body);
        Self::seal(&outline, params, body)
    }

    pub(crate) fn seal(
        outline: &ControlOutline,
        params: &[Param],
        body: &[Stmt],
    ) -> Result<Self, PlanError> {
        if !outline.structurally_matches(body) {
            return Err(PlanError {
                span: outline.declaration_span(),
                message: format!(
                    "checked body for {} no longer matches its pre-check control outline",
                    outline.owner().render()
                ),
            });
        }

        let mut scopes = Vec::with_capacity(outline.scopes.len());
        let mut scope_ids = HashMap::with_capacity(outline.scopes.len());
        for (index, source) in outline.scopes.iter().enumerate() {
            let id = ScopeId(index);
            let key = ScopeKey::new(outline.owner(), source.kind, source.anchor);
            if scope_ids.insert(key, id).is_some() {
                return Err(PlanError {
                    span: source.anchor,
                    message: format!("duplicate {:?} scope anchor in one callable", source.kind),
                });
            }
            scopes.push(Scope {
                parent: source.parent,
                kind: source.kind,
                anchor: source.anchor,
                locals: Vec::new(),
                bindings: Vec::new(),
                drops: Vec::new(),
            });
        }

        let mut builder = PlanBuilder {
            plan: Self {
                owner: outline.owner().clone(),
                blocks: outline.blocks.clone(),
                branches: Vec::new(),
                branch_ids: HashMap::new(),
                loops: Vec::new(),
                loop_ids: HashMap::new(),
                exposures: Vec::new(),
                exposure_ids: HashMap::new(),
                scopes,
                scope_ids,
                candidates: Vec::new(),
                candidate_ids: HashMap::new(),
                compiler_temps: HashMap::new(),
                assignments: Vec::new(),
                assignment_ids: HashMap::new(),
                field_assignments: Vec::new(),
                field_assignment_ids: HashMap::new(),
                temporary_drops: Vec::new(),
                temporary_drop_ids: HashMap::new(),
                return_sites: HashSet::new(),
                trap_sites: Vec::new(),
                trap_site_ids: HashMap::new(),
                frame_scope: outline.frame_scope(),
                body_scope: outline.body_scope(),
                body_block: outline.body_block(),
            },
            declared: HashSet::new(),
            bindings: HashMap::new(),
            exposure_depth: 0,
        };

        for param in params {
            builder.declare(
                outline.frame_scope(),
                &param.name,
                param.ty.clone(),
                param.span,
            )?;
        }
        builder.walk_block(body, outline.body_scope())?;
        let mut plan = builder.plan;
        plan.seal_structural_edges(outline, body, outline.body_block())?;
        plan.seal_trap_sites(body)?;
        plan.validate_callable(params, body)?;
        let trap = plan.trap_route();
        debug_assert_eq!(trap.kind(), ExitKind::Trap);
        debug_assert!(
            trap.scopes().is_empty() && trap.clears().is_empty() && trap.drops().is_empty()
        );
        Ok(plan)
    }

    fn seal_structural_edges(
        &mut self,
        outline: &ControlOutline,
        statements: &[Stmt],
        block: BlockId,
    ) -> Result<(), PlanError> {
        let planned = outline.block(block);
        if planned.statements().len() != statements.len() {
            return Err(PlanError {
                span: planned.anchor(),
                message: "checked block length no longer matches its pre-check outline".into(),
            });
        }

        for (index, statement) in statements.iter().enumerate() {
            match (outline.statement(block, index).kind(), statement) {
                (
                    StatementPlanKind::Branch(id),
                    Stmt::If {
                        cond,
                        then_block,
                        else_block,
                    },
                ) => {
                    let source = outline.branch(id).clone();
                    self.seal_structural_edges(outline, then_block, source.then_block())?;
                    if let (Some(statements), Some(child)) =
                        (else_block.as_deref(), source.else_block())
                    {
                        self.seal_structural_edges(outline, statements, child)?;
                    }

                    let arm = |plan: &Self, child: BlockId| {
                        let block = &plan.blocks[child.0];
                        BranchArmPlan {
                            block: child,
                            scope: block.scope(),
                            flow: block.flow(),
                            normal_exit: block
                                .flow()
                                .can_fall_through()
                                .then(|| plan.route(ExitKind::Fallthrough, [block.scope()])),
                        }
                    };
                    let branch = BranchPlan {
                        id,
                        parent_scope: source.parent_scope(),
                        anchor: source.anchor(),
                        then_arm: arm(self, source.then_block()),
                        else_arm: source.else_block().map(|child| arm(self, child)),
                        flow: source.flow(),
                    };
                    if branch.anchor != cond.span
                        || branch.else_arm.is_some() != else_block.is_some()
                    {
                        return Err(PlanError {
                            span: cond.span,
                            message: "checked branch no longer matches its pre-check arm shape"
                                .into(),
                        });
                    }
                    let key = BranchKey {
                        parent_scope: branch.parent_scope,
                        anchor: branch.anchor,
                    };
                    if self.branch_ids.insert(key, self.branches.len()).is_some() {
                        return Err(PlanError {
                            span: cond.span,
                            message: "duplicate branch site has no stable parent/anchor identity"
                                .into(),
                        });
                    }
                    if id.0 != self.branches.len() {
                        return Err(PlanError {
                            span: cond.span,
                            message: "pre-check branch identities changed during sealing".into(),
                        });
                    }
                    self.branches.push(branch);
                }
                (
                    StatementPlanKind::Loop(id),
                    Stmt::While {
                        cond,
                        kw_span,
                        body,
                        ..
                    },
                ) => {
                    let source = outline.loop_plan(id).clone();
                    self.seal_structural_edges(outline, body, source.body())?;
                    let body_plan = &self.blocks[source.body().0];
                    let loop_plan = LoopPlan {
                        id,
                        parent_scope: source.parent_scope(),
                        keyword_span: source.keyword_span(),
                        condition_span: source.condition_span(),
                        body: source.body(),
                        body_scope: body_plan.scope(),
                        body_flow: body_plan.flow(),
                        backedge: body_plan
                            .flow()
                            .can_fall_through()
                            .then(|| self.route(ExitKind::Backedge, [body_plan.scope()])),
                        effect_key: EffectSiteKey {
                            owner: self.owner.clone(),
                            span: source.keyword_span(),
                        },
                        flow: source.flow(),
                    };
                    if loop_plan.keyword_span != *kw_span || loop_plan.condition_span != cond.span {
                        return Err(PlanError {
                            span: *kw_span,
                            message: "checked loop no longer matches its pre-check edge identity"
                                .into(),
                        });
                    }
                    let key = LoopKey {
                        parent_scope: loop_plan.parent_scope,
                        keyword_span: loop_plan.keyword_span,
                    };
                    if self.loop_ids.insert(key, self.loops.len()).is_some() {
                        return Err(PlanError {
                            span: *kw_span,
                            message: "duplicate loop site has no stable parent/anchor identity"
                                .into(),
                        });
                    }
                    if id.0 != self.loops.len() {
                        return Err(PlanError {
                            span: *kw_span,
                            message: "pre-check loop identities changed during sealing".into(),
                        });
                    }
                    self.loops.push(loop_plan);
                }
                (
                    StatementPlanKind::Exposure(id),
                    Stmt::Expose {
                        kw_span,
                        array,
                        array_span,
                        mutable,
                        ptr,
                        res,
                        body,
                        ..
                    },
                ) => {
                    let source = outline.exposure(id).clone();
                    self.seal_structural_edges(outline, body, source.body())?;
                    let body_plan = &self.blocks[source.body().0];
                    let owner = Place::local(array);
                    let owner_ty = self
                        .scopes
                        .iter()
                        .flat_map(|scope| scope.bindings.iter())
                        .find(|binding| binding.place == owner)
                        .map(|binding| binding.ty.clone())
                        .ok_or_else(|| PlanError {
                            span: *kw_span,
                            message: format!(
                                "checked exposure source `{array}` has no retained binding"
                            ),
                        })?;
                    let mutability = if *mutable {
                        Mutability::Mut
                    } else {
                        Mutability::Shared
                    };
                    let normal = if body_plan.flow().can_fall_through() {
                        let body_exit = self.route(ExitKind::Fallthrough, [body_plan.scope()]);
                        let close = self.exposure_close(body_plan.scope(), *kw_span)?;
                        let release_loan = self
                            .compiler_temp(
                                body_plan.scope(),
                                *kw_span,
                                CompilerTempKind::ExposureLoan,
                            )?
                            .clone();
                        Some(ExposureNormalPlan {
                            capture: Place::local(res),
                            body_exit,
                            rebuild: ExposureRebuildAction {
                                owner,
                                owner_span: *array_span,
                                owner_ty,
                                mutability,
                                pointer: Place::local(ptr),
                                resource: Place::local(res),
                                keyword_span: *kw_span,
                            },
                            release_loan,
                            close,
                            parent_scope: source.parent_scope(),
                        })
                    } else {
                        None
                    };
                    let exposure = ExposurePlan {
                        id,
                        parent_scope: source.parent_scope(),
                        keyword_span: source.keyword_span(),
                        body: source.body(),
                        body_scope: body_plan.scope(),
                        body_flow: body_plan.flow(),
                        effect_key: EffectSiteKey {
                            owner: self.owner.clone(),
                            span: source.keyword_span(),
                        },
                        normal,
                        flow: source.flow(),
                    };
                    let key = ExposureKey {
                        parent_scope: exposure.parent_scope,
                        keyword_span: exposure.keyword_span,
                    };
                    if self
                        .exposure_ids
                        .insert(key, self.exposures.len())
                        .is_some()
                    {
                        return Err(PlanError {
                            span: *kw_span,
                            message: "duplicate exposure site has no stable parent/anchor identity"
                                .into(),
                        });
                    }
                    if id.0 != self.exposures.len() {
                        return Err(PlanError {
                            span: *kw_span,
                            message: "pre-check exposure identities changed during sealing".into(),
                        });
                    }
                    self.exposures.push(exposure);
                }
                (StatementPlanKind::Unsafe(child), Stmt::Unsafe { body, .. }) => {
                    self.seal_structural_edges(outline, body, child)?;
                }
                (StatementPlanKind::Return, Stmt::Return { .. })
                | (StatementPlanKind::Linear(LinearStatementKind::Decl), Stmt::Decl { .. })
                | (StatementPlanKind::Linear(LinearStatementKind::Assign), Stmt::Assign { .. })
                | (StatementPlanKind::Linear(LinearStatementKind::Expr), Stmt::ExprStmt(_))
                | (StatementPlanKind::Linear(LinearStatementKind::Assert), Stmt::Assert(_))
                | (StatementPlanKind::Linear(LinearStatementKind::VarDecl), Stmt::VarDecl { .. })
                | (
                    StatementPlanKind::Linear(LinearStatementKind::FieldAssign),
                    Stmt::FieldAssign { .. },
                )
                | (
                    StatementPlanKind::Linear(LinearStatementKind::FieldStore),
                    Stmt::FieldStore { .. },
                )
                | (StatementPlanKind::Linear(LinearStatementKind::Store), Stmt::Store { .. })
                | (
                    StatementPlanKind::Linear(LinearStatementKind::StaticAlloc),
                    Stmt::StaticAlloc { .. },
                )
                | (
                    StatementPlanKind::Linear(LinearStatementKind::SystemAlloc),
                    Stmt::SystemAlloc { .. },
                )
                | (
                    StatementPlanKind::Linear(LinearStatementKind::SystemDealloc),
                    Stmt::SystemDealloc { .. },
                ) => {}
                _ => {
                    return Err(PlanError {
                        span: planned.anchor(),
                        message: "checked statement no longer matches its pre-check control role"
                            .into(),
                    });
                }
            }
        }
        Ok(())
    }

    pub(crate) fn owner(&self) -> &CallOwner {
        &self.owner
    }

    pub(crate) const fn frame_scope(&self) -> ScopeId {
        self.frame_scope
    }

    pub(crate) const fn body_scope(&self) -> ScopeId {
        self.body_scope
    }

    pub(crate) fn body_block(&self) -> &BlockPlan {
        self.block(self.body_block)
    }

    pub(crate) fn block(&self, id: BlockId) -> &BlockPlan {
        &self.blocks[id.0]
    }

    pub(crate) fn branch(
        &self,
        parent_scope: ScopeId,
        anchor: Span,
        has_else: bool,
    ) -> Result<&BranchPlan, PlanError> {
        let Some(index) = self.branch_ids.get(&BranchKey {
            parent_scope,
            anchor,
        }) else {
            return Err(PlanError {
                span: anchor,
                message: "control plan has no branch in the active parent scope".into(),
            });
        };
        let plan = &self.branches[*index];
        if plan.else_arm().is_some() != has_else {
            return Err(PlanError {
                span: anchor,
                message: "checked branch else-arm presence changed after checking".into(),
            });
        }
        Ok(plan)
    }

    pub(crate) fn loop_plan(
        &self,
        parent_scope: ScopeId,
        keyword_span: Span,
        condition_span: Span,
    ) -> Result<&LoopPlan, PlanError> {
        let Some(index) = self.loop_ids.get(&LoopKey {
            parent_scope,
            keyword_span,
        }) else {
            return Err(PlanError {
                span: keyword_span,
                message: "control plan has no loop in the active parent scope".into(),
            });
        };
        let plan = &self.loops[*index];
        if plan.condition_span() != condition_span {
            return Err(PlanError {
                span: condition_span,
                message: "checked loop condition identity changed after checking".into(),
            });
        }
        Ok(plan)
    }

    pub(crate) fn exposure_plan(
        &self,
        parent_scope: ScopeId,
        keyword_span: Span,
    ) -> Result<&ExposurePlan, PlanError> {
        self.exposure_ids
            .get(&ExposureKey {
                parent_scope,
                keyword_span,
            })
            .map(|index| &self.exposures[*index])
            .ok_or_else(|| PlanError {
                span: keyword_span,
                message: "control plan has no exposure in the active parent scope".into(),
            })
    }

    pub(crate) fn scope_for(&self, kind: ScopeKind, anchor: Span) -> Result<ScopeId, PlanError> {
        self.scope_ids
            .get(&ScopeKey::new(&self.owner, kind, anchor))
            .copied()
            .ok_or_else(|| PlanError {
                span: anchor,
                message: format!("control plan has no {kind:?} scope at this anchor"),
            })
    }

    /// Parent identity for a resolved scope. Consumers pair this with
    /// [`BodyPlan::scope_for`] when validating that a checked structured edge
    /// has not been moved under a different lexical parent after checking.
    pub(crate) fn scope_parent(&self, scope: ScopeId) -> Option<ScopeId> {
        self.scopes[scope.0].parent
    }

    pub(crate) fn candidate(&self, id: DropId) -> &DropCandidate {
        &self.candidates[id.0]
    }

    pub(crate) fn candidate_for_place(&self, place: &Place) -> Option<&DropCandidate> {
        self.candidate_ids.get(place).map(|id| self.candidate(*id))
    }

    /// Cleanup for the ordinary end of one lexical scope. A loop body's
    /// ordinary end is its backedge; all other scopes fall through.
    pub(crate) fn scope_exit(&self, scope: ScopeId) -> ExitRoute {
        let kind = if self.scopes[scope.0].kind == ScopeKind::LoopBody {
            ExitKind::Backedge
        } else {
            ExitKind::Fallthrough
        };
        self.route(kind, [scope])
    }

    /// Explicit return routes, keyed by the return token span and the stable
    /// lexical scope the plan builder assigned it.
    pub(crate) fn explicit_return(
        &self,
        span: Span,
        scope: ScopeId,
    ) -> Result<ReturnRoutes, PlanError> {
        if !self.return_sites.contains(&(span, scope)) {
            return Err(PlanError {
                span,
                message: "control plan has no return at this span in the active lexical scope"
                    .into(),
            });
        }
        let slot = self
            .compiler_temps
            .get(&CompilerTempKey {
                scope,
                anchor: span,
                kind: CompilerTempKind::ReturnValue,
            })
            .cloned();
        Ok(self.return_from(scope, slot))
    }

    /// Falling off a callable body is the same two-phase cleanup as an
    /// explicit return, starting in the root body scope.
    pub(crate) fn implicit_return(&self) -> ReturnRoutes {
        self.return_from(self.body_scope, None)
    }

    /// Canonical empty no-unwind route shared by every retained trap site.
    /// Traps abort without lexical cleanup (ADRs 0029--0030).
    pub(crate) fn trap_route(&self) -> ExitRoute {
        ExitRoute::terminal_trap()
    }

    /// Exact direct trap sites for one expression at its active lexical scope.
    /// Recursive evaluation consumes child sites when it reaches those child
    /// expressions; this lookup therefore never speculates about a
    /// short-circuited or otherwise unevaluated descendant.
    pub(crate) fn expression_trap_sites(
        &self,
        scope: ScopeId,
        expression: &Expr,
    ) -> Result<Vec<&TrapSite>, PlanError> {
        direct_expression_traps(expression)?
            .into_iter()
            .map(|(span, kind)| self.trap_site(scope, span, kind))
            .collect()
    }

    /// Exact direct trap sites for one statement. Child-expression sites are
    /// consumed by expression evaluation/lowering. Structured child bodies
    /// similarly consume their own statement sites when entered.
    pub(crate) fn statement_trap_sites(
        &self,
        scope: ScopeId,
        statement: &Stmt,
    ) -> Result<Vec<&TrapSite>, PlanError> {
        direct_statement_traps(self, scope, statement)?
            .into_iter()
            .map(|key| self.trap_site(key.scope, key.span, key.kind))
            .collect()
    }

    /// Reconcile every structural table against the retained checked body.
    ///
    /// Dynamic consumers still perform exact per-operation lookups, but this
    /// complete ledger is what rejects deletion of an unreachable assignment,
    /// return, scope, or trap site. The walk is shared here so interpreter,
    /// LLVM, SVM, and future consumers cannot grow subtly different prepasses.
    pub(crate) fn validate_body_shape(&self, body: &[Stmt]) -> Result<(), PlanError> {
        self.validate_shape(None, body)
    }

    /// Full callable reconciliation, including ordered parameter bindings and
    /// their conditional drop candidates in the frame scope.
    pub(crate) fn validate_callable(
        &self,
        params: &[Param],
        body: &[Stmt],
    ) -> Result<(), PlanError> {
        self.validate_shape(Some(params), body)
    }

    fn validate_shape(&self, params: Option<&[Param]>, body: &[Stmt]) -> Result<(), PlanError> {
        self.validate_structural_body(body)?;

        let mut inventory = BodyInventory::default();
        inventory.scopes.insert(self.frame_scope);
        inventory.scopes.insert(self.body_scope);
        if let Some(params) = params {
            for parameter in params {
                inventory.source_binding(
                    self.frame_scope,
                    &parameter.name,
                    parameter.ty.clone(),
                    parameter.span,
                );
            }
        }
        self.inventory_block(body, self.body_scope, &mut inventory)?;

        if inventory.scopes.len() != self.scopes.len() {
            let missing = self
                .scopes
                .iter()
                .enumerate()
                .find(|(index, _)| !inventory.scopes.contains(&ScopeId(*index)))
                .map(|(_, scope)| scope)
                .expect("scope counts differ");
            return Err(PlanError {
                span: missing.anchor,
                message: format!(
                    "checked body no longer contains its planned {:?} scope",
                    missing.kind
                ),
            });
        }
        for (index, planned) in self.scopes.iter().enumerate() {
            let scope = ScopeId(index);
            if scope == self.frame_scope && params.is_none() {
                continue;
            }
            let expected_locals = inventory.locals.get(&scope).map_or(&[][..], Vec::as_slice);
            if planned.locals.as_slice() != expected_locals {
                return Err(PlanError {
                    span: planned.anchor,
                    message: format!(
                        "checked {:?} scope bindings no longer match its ordered control plan",
                        planned.kind
                    ),
                });
            }
            let expected_bindings = inventory
                .bindings
                .get(&scope)
                .map_or(&[][..], Vec::as_slice);
            if planned.bindings.as_slice() != expected_bindings {
                let span = expected_bindings
                    .first()
                    .map_or(planned.anchor, |binding| binding.span);
                return Err(PlanError {
                    span,
                    message: format!(
                        "checked {:?} source bindings no longer match their names, types, or declaration spans",
                        planned.kind
                    ),
                });
            }

            let mut expected_drops = Vec::new();
            for binding in expected_bindings {
                let candidate = self.candidate_for_place(&binding.place);
                let expected_action = ValueDropAction::build(&binding.ty, binding.span)?;
                if let Some(expected_action) = expected_action {
                    let Some(candidate) = candidate else {
                        return Err(PlanError {
                            span: binding.span,
                            message: format!(
                                "cleanup-bearing binding `{}` has no planned drop candidate",
                                binding.place.render()
                            ),
                        });
                    };
                    if candidate.scope() != scope
                        || candidate.drop_action() != &expected_action
                        || candidate.span() != binding.span
                    {
                        return Err(PlanError {
                            span: binding.span,
                            message: format!(
                                "drop candidate for `{}` no longer matches its checked binding",
                                binding.place.render()
                            ),
                        });
                    }
                    expected_drops.push(candidate.id());
                } else if candidate.is_some() {
                    return Err(PlanError {
                        span: binding.span,
                        message: format!(
                            "non-cleanup binding `{}` retained a stale drop candidate",
                            binding.place.render()
                        ),
                    });
                }
            }
            if planned.drops != expected_drops {
                return Err(PlanError {
                    span: planned.anchor,
                    message: format!(
                        "checked {:?} drop candidates no longer match declaration order",
                        planned.kind
                    ),
                });
            }
        }
        if inventory.assignments.len() != self.assignments.len() {
            let missing = self
                .assignment_ids
                .iter()
                .find(|(key, _)| !inventory.assignments.contains(key))
                .map(|(key, _)| *key)
                .expect("assignment counts differ");
            return Err(PlanError {
                span: missing.span,
                message: "checked body no longer contains its planned assignment".into(),
            });
        }
        if inventory.field_assignments.len() != self.field_assignments.len() {
            let missing = self
                .field_assignment_ids
                .iter()
                .find(|(key, _)| !inventory.field_assignments.contains(key))
                .map(|(key, _)| *key)
                .expect("field-assignment counts differ");
            return Err(PlanError {
                span: missing.span,
                message: "checked body no longer contains its planned field assignment".into(),
            });
        }
        if inventory.temporary_drops.len() != self.temporary_drops.len() {
            let missing = self
                .temporary_drop_ids
                .iter()
                .find(|(key, _)| !inventory.temporary_drops.contains(key))
                .map(|(key, _)| *key)
                .expect("temporary-drop counts differ");
            return Err(PlanError {
                span: missing.span,
                message: "checked body no longer contains its planned discarded class temporary"
                    .into(),
            });
        }
        if inventory.returns.len() != self.return_sites.len() {
            let missing = self
                .return_sites
                .iter()
                .find(|site| !inventory.returns.contains(site))
                .copied()
                .expect("return counts differ");
            return Err(PlanError {
                span: missing.0,
                message: "checked body no longer contains its planned return".into(),
            });
        }
        if inventory.compiler_temps.len() != self.compiler_temps.len()
            || inventory
                .compiler_temps
                .iter()
                .any(|key| !self.compiler_temps.contains_key(key))
        {
            let span = self
                .compiler_temps
                .keys()
                .find(|key| !inventory.compiler_temps.contains(key))
                .map_or(self.scopes[self.body_scope.0].anchor, |key| key.anchor);
            return Err(PlanError {
                span,
                message: "checked body no longer contains its exact compiler-temporary sites"
                    .into(),
            });
        }

        let mut visited_traps = HashSet::new();
        for key in inventory.traps {
            let site = self.trap_site(key.scope, key.span, key.kind)?;
            let index = self
                .trap_site_ids
                .get(&site.key)
                .copied()
                .expect("trap_site returned a retained site");
            if !visited_traps.insert(index) {
                return Err(PlanError {
                    span: site.span(),
                    message: "two source operations reuse one checked trap-site identity".into(),
                });
            }
        }
        if visited_traps.len() != self.trap_sites.len() {
            let missing = self
                .trap_sites
                .iter()
                .enumerate()
                .find(|(index, _)| !visited_traps.contains(index))
                .map(|(_, site)| site)
                .expect("trap-site counts differ");
            return Err(PlanError {
                span: missing.span(),
                message: "checked body no longer contains its planned trap site".into(),
            });
        }
        Ok(())
    }

    /// Reconcile the checked statement tree against the retained structural
    /// graph before collecting bindings, drops, assignments, or trap sites.
    ///
    /// The walk follows sealed `BlockId`/edge identities. Source syntax tells
    /// us which retained statement role must be present, but it is not rebuilt
    /// into a second outline and cannot become an alternate control authority.
    fn validate_structural_body(&self, body: &[Stmt]) -> Result<(), PlanError> {
        self.validate_structural_tables()?;

        let declaration_span = self
            .scopes
            .get(self.body_scope.0)
            .map(|scope| scope.anchor)
            .unwrap_or(Span::new(0, 0));
        let mut visited = StructuralInventory::default();
        self.validate_structural_scope(
            self.frame_scope,
            ScopeKind::Frame,
            declaration_span,
            None,
            &mut visited,
        )?;
        self.validate_structural_scope(
            self.body_scope,
            ScopeKind::Body,
            declaration_span,
            Some(self.frame_scope),
            &mut visited,
        )?;
        self.validate_structural_block(
            body,
            self.body_block,
            None,
            BlockKind::Body,
            declaration_span,
            self.body_scope,
            &mut visited,
        )?;

        if visited.blocks.len() != self.blocks.len() {
            let missing = self
                .blocks
                .iter()
                .find(|block| !visited.blocks.contains(&block.id))
                .expect("block counts differ");
            return Err(PlanError {
                span: missing.anchor,
                message: "checked body no longer reaches every retained structural block".into(),
            });
        }
        if visited.branches.len() != self.branches.len() {
            let missing = self
                .branches
                .iter()
                .find(|branch| !visited.branches.contains(&branch.id))
                .expect("branch counts differ");
            return Err(PlanError {
                span: missing.anchor,
                message: "checked body no longer reaches every retained branch edge".into(),
            });
        }
        if visited.loops.len() != self.loops.len() {
            let missing = self
                .loops
                .iter()
                .find(|loop_plan| !visited.loops.contains(&loop_plan.id))
                .expect("loop counts differ");
            return Err(PlanError {
                span: missing.keyword_span,
                message: "checked body no longer reaches every retained loop edge".into(),
            });
        }
        if visited.exposures.len() != self.exposures.len() {
            let missing = self
                .exposures
                .iter()
                .find(|exposure| !visited.exposures.contains(&exposure.id))
                .expect("exposure counts differ");
            return Err(PlanError {
                span: missing.keyword_span,
                message: "checked body no longer reaches every retained exposure edge".into(),
            });
        }
        if visited.scopes.len() != self.scopes.len() {
            let missing = self
                .scopes
                .iter()
                .enumerate()
                .find(|(index, _)| !visited.scopes.contains(&ScopeId(*index)))
                .map(|(_, scope)| scope)
                .expect("scope counts differ");
            return Err(PlanError {
                span: missing.anchor,
                message: format!(
                    "checked body no longer reaches its retained {:?} structural scope",
                    missing.kind
                ),
            });
        }
        Ok(())
    }

    fn validate_structural_tables(&self) -> Result<(), PlanError> {
        let fallback = self
            .scopes
            .get(self.body_scope.0)
            .map_or(Span::new(0, 0), |scope| scope.anchor);
        if self.branch_ids.len() != self.branches.len()
            || self.loop_ids.len() != self.loops.len()
            || self.exposure_ids.len() != self.exposures.len()
            || self.scope_ids.len() != self.scopes.len()
        {
            return Err(PlanError {
                span: fallback,
                message: "retained structural index cardinality no longer matches its plan table"
                    .into(),
            });
        }
        for (index, block) in self.blocks.iter().enumerate() {
            if block.id != BlockId(index) {
                return Err(PlanError {
                    span: block.anchor,
                    message: "retained block identity no longer matches its table position".into(),
                });
            }
        }
        for (index, branch) in self.branches.iter().enumerate() {
            let key = BranchKey {
                parent_scope: branch.parent_scope,
                anchor: branch.anchor,
            };
            if branch.id != BranchId(index) || self.branch_ids.get(&key) != Some(&index) {
                return Err(PlanError {
                    span: branch.anchor,
                    message: "retained branch identity no longer matches its exact index".into(),
                });
            }
        }
        for (index, loop_plan) in self.loops.iter().enumerate() {
            let key = LoopKey {
                parent_scope: loop_plan.parent_scope,
                keyword_span: loop_plan.keyword_span,
            };
            if loop_plan.id != LoopId(index) || self.loop_ids.get(&key) != Some(&index) {
                return Err(PlanError {
                    span: loop_plan.keyword_span,
                    message: "retained loop identity no longer matches its exact index".into(),
                });
            }
        }
        for (index, exposure) in self.exposures.iter().enumerate() {
            let key = ExposureKey {
                parent_scope: exposure.parent_scope,
                keyword_span: exposure.keyword_span,
            };
            if exposure.id != ExposureId(index) || self.exposure_ids.get(&key) != Some(&index) {
                return Err(PlanError {
                    span: exposure.keyword_span,
                    message: "retained exposure identity no longer matches its exact index".into(),
                });
            }
        }
        for (index, scope) in self.scopes.iter().enumerate() {
            let id = ScopeId(index);
            let key = ScopeKey::new(&self.owner, scope.kind, scope.anchor);
            if self.scope_ids.get(&key) != Some(&id) {
                return Err(PlanError {
                    span: scope.anchor,
                    message: format!(
                        "retained {:?} scope no longer matches its exact index",
                        scope.kind
                    ),
                });
            }
        }
        Ok(())
    }

    fn validate_structural_scope(
        &self,
        id: ScopeId,
        kind: ScopeKind,
        anchor: Span,
        parent: Option<ScopeId>,
        visited: &mut StructuralInventory,
    ) -> Result<(), PlanError> {
        let Some(scope) = self.scopes.get(id.0) else {
            return Err(PlanError {
                span: anchor,
                message: format!("retained {kind:?} scope identity is out of range"),
            });
        };
        if !visited.scopes.insert(id) {
            return Err(PlanError {
                span: anchor,
                message: format!(
                    "two retained {kind:?} blocks reuse one checked structural identity"
                ),
            });
        }
        if scope.kind != kind || scope.anchor != anchor || scope.parent != parent {
            return Err(PlanError {
                span: anchor,
                message: format!(
                    "checked {kind:?} scope no longer matches its retained parent or anchor"
                ),
            });
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_structural_block(
        &self,
        statements: &[Stmt],
        id: BlockId,
        parent: Option<BlockId>,
        kind: BlockKind,
        anchor: Span,
        scope: ScopeId,
        visited: &mut StructuralInventory,
    ) -> Result<FlowSummary, PlanError> {
        let Some(block) = self.blocks.get(id.0) else {
            return Err(PlanError {
                span: anchor,
                message: "retained structural block identity is out of range".into(),
            });
        };
        if !visited.blocks.insert(id) {
            return Err(PlanError {
                span: anchor,
                message: "two source blocks reuse one retained BlockId".into(),
            });
        }
        if block.id != id
            || block.parent != parent
            || block.kind != kind
            || block.anchor != anchor
            || block.scope != scope
        {
            return Err(PlanError {
                span: anchor,
                message: "checked block no longer matches its retained identity, parent, scope, kind, or anchor"
                    .into(),
            });
        }
        if block.statements.len() != statements.len() {
            return Err(PlanError {
                span: anchor,
                message: "checked block statement count changed within its active lexical scope; a subtree may have moved under a different lexical parent, source structure may reuse one checked structural identity, no assignment at this span may exist, or a planned assignment / planned trap site may remain"
                    .into(),
            });
        }

        let mut flow = FlowSummary::FALLTHROUGH;
        for (statement, planned) in statements.iter().zip(&block.statements) {
            let expected_entry = flow.reaches_next;
            let statement_flow =
                self.validate_structural_statement(statement, planned.kind, id, scope, visited)?;
            if planned.entry_reachable != expected_entry || planned.flow != statement_flow {
                return Err(PlanError {
                    span: anchor,
                    message: "retained statement reachability or flow no longer matches its structural edge"
                        .into(),
                });
            }
            flow.contains_return |= statement_flow.contains_return;
            if expected_entry {
                flow.has_reachable_return |= statement_flow.has_reachable_return;
                flow.reaches_next = statement_flow.reaches_next;
            }
        }
        if block.flow != flow {
            return Err(PlanError {
                span: anchor,
                message: "retained block flow no longer matches its ordered statements".into(),
            });
        }
        Ok(flow)
    }

    fn validate_structural_statement(
        &self,
        statement: &Stmt,
        kind: StatementPlanKind,
        parent_block: BlockId,
        parent_scope: ScopeId,
        visited: &mut StructuralInventory,
    ) -> Result<FlowSummary, PlanError> {
        match (kind, statement) {
            (StatementPlanKind::Return, Stmt::Return { .. }) => Ok(FlowSummary {
                reaches_next: false,
                has_reachable_return: true,
                contains_return: true,
            }),
            (
                StatementPlanKind::Branch(id),
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                },
            ) => self.validate_structural_branch(
                id,
                parent_block,
                parent_scope,
                cond.span,
                then_block,
                else_block.as_deref(),
                visited,
            ),
            (
                StatementPlanKind::Loop(id),
                Stmt::While {
                    cond,
                    kw_span,
                    body,
                    ..
                },
            ) => self.validate_structural_loop(
                id,
                parent_block,
                parent_scope,
                *kw_span,
                cond.span,
                body,
                visited,
            ),
            (
                StatementPlanKind::Exposure(id),
                Stmt::Expose {
                    kw_span,
                    array,
                    array_span,
                    mutable,
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    body,
                },
            ) => self.validate_structural_exposure(
                id,
                parent_block,
                parent_scope,
                *kw_span,
                array,
                *array_span,
                *mutable,
                ptr,
                *ptr_span,
                res,
                *res_span,
                body,
                visited,
            ),
            (StatementPlanKind::Unsafe(child), Stmt::Unsafe { kw_span, body }) => self
                .validate_structural_block(
                    body,
                    child,
                    Some(parent_block),
                    BlockKind::Unsafe,
                    *kw_span,
                    parent_scope,
                    visited,
                ),
            (StatementPlanKind::Linear(expected), source)
                if Self::linear_statement_kind(source) == Some(expected) =>
            {
                Ok(FlowSummary::FALLTHROUGH)
            }
            _ => Err(PlanError {
                span: self
                    .blocks
                    .get(parent_block.0)
                    .map_or(Span::new(0, 0), |block| block.anchor),
                message: "checked statement no longer matches its retained control role".into(),
            }),
        }
    }

    fn linear_statement_kind(statement: &Stmt) -> Option<LinearStatementKind> {
        match statement {
            Stmt::Decl { .. } => Some(LinearStatementKind::Decl),
            Stmt::Assign { .. } => Some(LinearStatementKind::Assign),
            Stmt::ExprStmt(_) => Some(LinearStatementKind::Expr),
            Stmt::Assert(_) => Some(LinearStatementKind::Assert),
            Stmt::VarDecl { .. } => Some(LinearStatementKind::VarDecl),
            Stmt::FieldAssign { .. } => Some(LinearStatementKind::FieldAssign),
            Stmt::FieldStore { .. } => Some(LinearStatementKind::FieldStore),
            Stmt::Store { .. } => Some(LinearStatementKind::Store),
            Stmt::StaticAlloc { .. } => Some(LinearStatementKind::StaticAlloc),
            Stmt::SystemAlloc { .. } => Some(LinearStatementKind::SystemAlloc),
            Stmt::SystemDealloc { .. } => Some(LinearStatementKind::SystemDealloc),
            Stmt::If { .. }
            | Stmt::Return { .. }
            | Stmt::While { .. }
            | Stmt::Unsafe { .. }
            | Stmt::Expose { .. } => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_structural_branch(
        &self,
        id: BranchId,
        parent_block: BlockId,
        parent_scope: ScopeId,
        anchor: Span,
        then_body: &[Stmt],
        else_body: Option<&[Stmt]>,
        visited: &mut StructuralInventory,
    ) -> Result<FlowSummary, PlanError> {
        let Some(branch) = self.branches.get(id.0) else {
            return Err(PlanError {
                span: anchor,
                message: "retained branch identity is out of range".into(),
            });
        };
        if !visited.branches.insert(id) {
            return Err(PlanError {
                span: anchor,
                message: "two source branches reuse one retained BranchId".into(),
            });
        }
        match (branch.else_arm.is_some(), else_body.is_some()) {
            (false, true) => {
                return Err(PlanError {
                    span: anchor,
                    message: "checked body gained an unplanned else scope".into(),
                });
            }
            (true, false) => {
                return Err(PlanError {
                    span: anchor,
                    message: "checked body no longer contains its planned else scope".into(),
                });
            }
            _ => {}
        }
        if branch.id != id || branch.parent_scope != parent_scope || branch.anchor != anchor {
            return Err(PlanError {
                span: anchor,
                message: "checked branch no longer matches its retained parent or anchor".into(),
            });
        }

        let then_flow = self.validate_structural_branch_arm(
            branch.then_arm(),
            BranchArm::Then,
            parent_block,
            parent_scope,
            anchor,
            then_body,
            visited,
        )?;
        let else_flow = match (branch.else_arm(), else_body) {
            (Some(arm), Some(body)) => self.validate_structural_branch_arm(
                arm,
                BranchArm::Else,
                parent_block,
                parent_scope,
                anchor,
                body,
                visited,
            )?,
            (None, None) => FlowSummary::FALLTHROUGH,
            _ => unreachable!("else presence was checked above"),
        };
        let flow = FlowSummary {
            reaches_next: then_flow.reaches_next || else_flow.reaches_next,
            has_reachable_return: then_flow.has_reachable_return || else_flow.has_reachable_return,
            contains_return: then_flow.contains_return || else_flow.contains_return,
        };
        if branch.flow != flow {
            return Err(PlanError {
                span: anchor,
                message: "retained branch flow no longer matches its exact arm flows".into(),
            });
        }
        Ok(flow)
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_structural_branch_arm(
        &self,
        arm: &BranchArmPlan,
        which: BranchArm,
        parent_block: BlockId,
        parent_scope: ScopeId,
        anchor: Span,
        body: &[Stmt],
        visited: &mut StructuralInventory,
    ) -> Result<FlowSummary, PlanError> {
        self.validate_structural_scope(
            arm.scope,
            ScopeKind::BranchArm(which),
            anchor,
            Some(parent_scope),
            visited,
        )?;
        let flow = self.validate_structural_block(
            body,
            arm.block,
            Some(parent_block),
            BlockKind::BranchArm(which),
            anchor,
            arm.scope,
            visited,
        )?;
        let expected_exit = flow
            .can_fall_through()
            .then(|| self.route(ExitKind::Fallthrough, [arm.scope]));
        if arm.flow != flow || arm.normal_exit.as_ref() != expected_exit.as_ref() {
            return Err(PlanError {
                span: anchor,
                message: format!(
                    "retained {which:?} arm flow or normal exit no longer matches its child block"
                ),
            });
        }
        Ok(flow)
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_structural_loop(
        &self,
        id: LoopId,
        parent_block: BlockId,
        parent_scope: ScopeId,
        keyword_span: Span,
        condition_span: Span,
        body: &[Stmt],
        visited: &mut StructuralInventory,
    ) -> Result<FlowSummary, PlanError> {
        let Some(loop_plan) = self.loops.get(id.0) else {
            return Err(PlanError {
                span: keyword_span,
                message: "retained loop identity is out of range".into(),
            });
        };
        if !visited.loops.insert(id) {
            return Err(PlanError {
                span: keyword_span,
                message: "two source loops reuse one retained LoopId".into(),
            });
        }
        let expected_effect = EffectSiteKey {
            owner: self.owner.clone(),
            span: keyword_span,
        };
        if loop_plan.id != id
            || loop_plan.parent_scope != parent_scope
            || loop_plan.keyword_span != keyword_span
            || loop_plan.condition_span != condition_span
            || loop_plan.effect_key != expected_effect
        {
            return Err(PlanError {
                span: keyword_span,
                message: "checked loop no longer matches its retained parent, header, condition, or effect identity"
                    .into(),
            });
        }
        self.validate_structural_scope(
            loop_plan.body_scope,
            ScopeKind::LoopBody,
            keyword_span,
            Some(parent_scope),
            visited,
        )?;
        let body_flow = self.validate_structural_block(
            body,
            loop_plan.body,
            Some(parent_block),
            BlockKind::LoopBody,
            keyword_span,
            loop_plan.body_scope,
            visited,
        )?;
        let expected_backedge = body_flow
            .can_fall_through()
            .then(|| self.route(ExitKind::Backedge, [loop_plan.body_scope]));
        let flow = FlowSummary {
            reaches_next: true,
            has_reachable_return: body_flow.has_reachable_return,
            contains_return: body_flow.contains_return,
        };
        if loop_plan.body_flow != body_flow
            || loop_plan.backedge.as_ref() != expected_backedge.as_ref()
            || loop_plan.flow != flow
        {
            return Err(PlanError {
                span: keyword_span,
                message:
                    "retained loop body flow, backedge, or continuation flow no longer matches"
                        .into(),
            });
        }
        Ok(flow)
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_structural_exposure(
        &self,
        id: ExposureId,
        parent_block: BlockId,
        parent_scope: ScopeId,
        keyword_span: Span,
        owner_name: &str,
        owner_span: Span,
        mutable: bool,
        pointer_name: &str,
        pointer_span: Span,
        resource_name: &str,
        resource_span: Span,
        body: &[Stmt],
        visited: &mut StructuralInventory,
    ) -> Result<FlowSummary, PlanError> {
        let Some(exposure) = self.exposures.get(id.0) else {
            return Err(PlanError {
                span: keyword_span,
                message: "retained exposure identity is out of range".into(),
            });
        };
        if !visited.exposures.insert(id) {
            return Err(PlanError {
                span: keyword_span,
                message: "two source exposures reuse one retained ExposureId".into(),
            });
        }
        let expected_effect = EffectSiteKey {
            owner: self.owner.clone(),
            span: keyword_span,
        };
        if exposure.id != id
            || exposure.parent_scope != parent_scope
            || exposure.keyword_span != keyword_span
            || exposure.effect_key != expected_effect
        {
            return Err(PlanError {
                span: keyword_span,
                message: "checked exposure no longer matches its retained parent, anchor, or effect identity"
                    .into(),
            });
        }
        self.validate_structural_scope(
            exposure.body_scope,
            ScopeKind::Exposure,
            keyword_span,
            Some(parent_scope),
            visited,
        )?;
        self.validate_structural_exposure_binding(
            exposure.body_scope,
            0,
            pointer_name,
            Ty::Raw(IntTy::U8),
            pointer_span,
        )?;
        self.validate_structural_exposure_binding(
            exposure.body_scope,
            1,
            resource_name,
            Ty::Res(ResKind::RawSpan),
            resource_span,
        )?;
        let body_flow = self.validate_structural_block(
            body,
            exposure.body,
            Some(parent_block),
            BlockKind::Exposure,
            keyword_span,
            exposure.body_scope,
            visited,
        )?;
        if exposure.body_flow != body_flow || exposure.flow != body_flow {
            return Err(PlanError {
                span: keyword_span,
                message: "retained exposure body or continuation flow no longer matches".into(),
            });
        }

        let owner = Place::local(owner_name);
        let owner_ty = self.retained_binding_type(&owner, owner_span)?;
        let expected_mutability = if mutable {
            Mutability::Mut
        } else {
            Mutability::Shared
        };
        match (exposure.normal.as_ref(), body_flow.can_fall_through()) {
            (Some(normal), true) => {
                let expected_body_exit = self.route(ExitKind::Fallthrough, [exposure.body_scope]);
                let expected_close = self.exposure_close(exposure.body_scope, keyword_span)?;
                let expected_release = self.compiler_temp(
                    exposure.body_scope,
                    keyword_span,
                    CompilerTempKind::ExposureLoan,
                )?;
                let rebuild = normal.rebuild();
                if normal.capture() != &Place::local(resource_name)
                    || normal.body_exit() != &expected_body_exit
                    || rebuild.owner() != &owner
                    || rebuild.owner_span() != owner_span
                    || rebuild.owner_ty() != owner_ty
                    || rebuild.mutability() != expected_mutability
                    || rebuild.pointer() != &Place::local(pointer_name)
                    || rebuild.resource() != &Place::local(resource_name)
                    || rebuild.keyword_span() != keyword_span
                    || normal.release_loan() != expected_release
                    || normal.close() != &expected_close
                    || normal.parent_scope() != parent_scope
                {
                    return Err(PlanError {
                        span: keyword_span,
                        message: "checked exposure owner, type, mutability, bindings, or ordered normal phases no longer match the retained plan"
                            .into(),
                    });
                }
            }
            (None, false) => {}
            _ => {
                return Err(PlanError {
                    span: keyword_span,
                    message: "retained exposure normal-edge presence no longer matches body flow"
                        .into(),
                });
            }
        }
        Ok(body_flow)
    }

    fn validate_structural_exposure_binding(
        &self,
        scope: ScopeId,
        index: usize,
        name: &str,
        ty: Ty,
        span: Span,
    ) -> Result<(), PlanError> {
        let Some(binding) = self
            .scopes
            .get(scope.0)
            .and_then(|scope| scope.bindings.get(index))
        else {
            return Err(PlanError {
                span,
                message: "retained exposure is missing one of its body bindings".into(),
            });
        };
        let expected = SourceBinding {
            place: Place::local(name),
            ty,
            span,
        };
        if binding != &expected {
            return Err(PlanError {
                span,
                message: "checked exposure pointer/resource binding no longer matches its retained name, type, or span"
                    .into(),
            });
        }
        Ok(())
    }

    fn retained_binding_type<'a>(&'a self, place: &Place, span: Span) -> Result<&'a Ty, PlanError> {
        let mut matches = self
            .scopes
            .iter()
            .flat_map(|scope| scope.bindings.iter())
            .filter(|binding| &binding.place == place);
        let Some(binding) = matches.next() else {
            return Err(PlanError {
                span,
                message: format!(
                    "checked exposure owner `{}` has no retained source binding",
                    place.render()
                ),
            });
        };
        if matches.next().is_some() {
            return Err(PlanError {
                span,
                message: format!(
                    "checked exposure owner `{}` has ambiguous retained source bindings",
                    place.render()
                ),
            });
        }
        Ok(&binding.ty)
    }

    pub(crate) fn compiler_temp(
        &self,
        scope: ScopeId,
        anchor: Span,
        kind: CompilerTempKind,
    ) -> Result<&Place, PlanError> {
        self.compiler_temps
            .get(&CompilerTempKey {
                scope,
                anchor,
                kind,
            })
            .ok_or_else(|| PlanError {
                span: anchor,
                message: format!("control plan has no {kind:?} temporary in the active scope"),
            })
    }

    /// Resolve one assignment by its lexical scope and assignment-token span.
    /// The destination is checked as part of lookup so a mutated AST cannot
    /// reuse a valid site's replacement action for another local.
    pub(crate) fn assignment(
        &self,
        scope: ScopeId,
        span: Span,
        destination: &Place,
    ) -> Result<&AssignmentAction, PlanError> {
        let Some(index) = self.assignment_ids.get(&AssignmentKey { scope, span }) else {
            return Err(PlanError {
                span,
                message: "control plan has no assignment at this span in the active lexical scope"
                    .into(),
            });
        };
        let action = &self.assignments[*index];
        if action.destination() != destination {
            return Err(PlanError {
                span,
                message: format!(
                    "control assignment at this span targets `{}`, not `{}`",
                    action.destination().render(),
                    destination.render()
                ),
            });
        }
        Ok(action)
    }

    pub(crate) fn assignments(&self) -> impl ExactSizeIterator<Item = &AssignmentAction> {
        self.assignments.iter()
    }

    /// Resolve one `self.field = value` replacement/install sequence.
    ///
    /// The field token anchors the statement action, while the checked RHS
    /// type and span participate through the checker-authored transfer key.
    /// This makes both destination substitution and value respanning fail
    /// before a consumer evaluates or lowers the RHS.
    pub(crate) fn field_assignment(
        &self,
        scope: ScopeId,
        span: Span,
        destination: &Place,
        value: &Expr,
    ) -> Result<&FieldAssignmentAction, PlanError> {
        let Some(index) = self
            .field_assignment_ids
            .get(&FieldAssignmentKey { scope, span })
        else {
            return Err(PlanError {
                span,
                message:
                    "control plan has no field assignment at this span in the active lexical scope"
                        .into(),
            });
        };
        let action = self
            .field_assignments
            .get(*index)
            .ok_or_else(|| PlanError {
                span,
                message: "field-assignment index no longer resolves to a retained action".into(),
            })?;
        let value_ty = checked_expression_ty(value, "field-assignment value")?;
        let transfer_key = ValueTransferKey {
            owner: self.owner.clone(),
            span: value.span,
            sink: ValueTransferSink::FieldAssignment(destination.clone()),
        };
        let expected_drop_action = ValueDropAction::build(&value_ty, span)?;
        if action.scope != scope
            || action.span != span
            || action.destination != *destination
            || action.ty != value_ty
            || action.transfer_key != transfer_key
            || action.drop_action != expected_drop_action
        {
            return Err(PlanError {
                span,
                message: format!(
                    "control field assignment no longer matches destination `{}`, checked RHS type/span, or transfer identity",
                    destination.render()
                ),
            });
        }
        let expected_staging = if expected_drop_action.is_some() {
            AssignmentStaging::Temporary(
                self.compiler_temp(scope, span, CompilerTempKind::FieldAssignmentValue)?
                    .clone(),
            )
        } else {
            AssignmentStaging::Direct
        };
        if action.staging != expected_staging {
            return Err(PlanError {
                span,
                message: "field-assignment staging no longer matches its checked cleanup policy"
                    .into(),
            });
        }
        Ok(action)
    }

    pub(crate) fn field_assignments(
        &self,
    ) -> impl ExactSizeIterator<Item = &FieldAssignmentAction> {
        self.field_assignments.iter()
    }

    /// Resolve a discarded fresh class value and its statement-end drop.
    pub(crate) fn temporary_drop(
        &self,
        scope: ScopeId,
        expression: &Expr,
    ) -> Result<&TemporaryDropAction, PlanError> {
        let span = expression.span;
        let Some(index) = self
            .temporary_drop_ids
            .get(&TemporaryDropKey { scope, span })
        else {
            return Err(PlanError {
                span,
                message:
                    "control plan has no discarded class temporary at this span in the active lexical scope"
                        .into(),
            });
        };
        if let Some(source) = Place::from_value_expr(expression) {
            return Err(PlanError {
                span,
                message: format!(
                    "discarded class temporary unexpectedly names source place `{}`",
                    source.render()
                ),
            });
        }
        let ty = checked_expression_ty(expression, "discarded class temporary")?;
        let action = self.temporary_drops.get(*index).ok_or_else(|| PlanError {
            span,
            message: "discarded-class index no longer resolves to a retained action".into(),
        })?;
        let expected_temporary =
            self.compiler_temp(scope, span, CompilerTempKind::DiscardedClassValue)?;
        let transfer_key = ValueTransferKey {
            owner: self.owner.clone(),
            span,
            sink: ValueTransferSink::DiscardTemporary,
        };
        let expected_drop_action = ValueDropAction::build(&ty, span)?;
        match (&ty, expected_drop_action) {
            (Ty::Class(_), Some(expected_drop_action))
                if action.scope == scope
                    && action.span == span
                    && action.drop_action == expected_drop_action
                    && action.transfer_key == transfer_key
                    && action.temporary == *expected_temporary =>
            {
                Ok(action)
            }
            (Ty::Class(_), _) => Err(PlanError {
                span,
                message:
                    "discarded class temporary no longer matches its type, compiler temporary, or terminal drop action"
                        .into(),
            }),
            (_, _) => Err(PlanError {
                span,
                message: "discarded temporary action no longer targets a class value".into(),
            }),
        }
    }

    pub(crate) fn temporary_drops(&self) -> impl ExactSizeIterator<Item = &TemporaryDropAction> {
        self.temporary_drops.iter()
    }

    /// Compiler-only exposure scratch survives the lexical body close because
    /// reconstruction still needs it. This route runs only after copyback and
    /// raw release have completed normally; a trap skips it with the rest of
    /// the exposure epilogue.
    pub(crate) fn exposure_close(
        &self,
        scope: ScopeId,
        anchor: Span,
    ) -> Result<ExitRoute, PlanError> {
        let clears = [
            CompilerTempKind::ExposureByte,
            CompilerTempKind::ExposureIndex,
            CompilerTempKind::ExposureLoan,
        ]
        .into_iter()
        .map(|kind| self.compiler_temp(scope, anchor, kind).cloned())
        .collect::<Result<Vec<_>, _>>()?;
        Ok(ExitRoute {
            kind: ExitKind::ExposureClose,
            scopes: Vec::new(),
            clears,
            drops: Vec::new(),
        })
    }

    fn return_from(&self, start: ScopeId, result_slot: Option<Place>) -> ReturnRoutes {
        let mut lexical_scopes = Vec::new();
        let mut cursor = Some(start);
        while let Some(scope) = cursor {
            if scope == self.frame_scope {
                break;
            }
            lexical_scopes.push(scope);
            cursor = self.scopes[scope.0].parent;
        }
        ReturnRoutes {
            lexical: self.route(ExitKind::Return, lexical_scopes),
            frame: self.route(ExitKind::Return, [self.frame_scope]),
            result_slot,
        }
    }

    fn route(&self, kind: ExitKind, scopes: impl IntoIterator<Item = ScopeId>) -> ExitRoute {
        let scopes: Vec<ScopeId> = scopes.into_iter().collect();
        let drops = scopes
            .iter()
            .flat_map(|scope| self.scopes[scope.0].drops.iter().rev().copied())
            .collect();
        let clears = scopes
            .iter()
            .flat_map(|scope| self.scopes[scope.0].locals.iter().rev().cloned())
            .collect();
        ExitRoute {
            kind,
            scopes,
            clears,
            drops,
        }
    }

    fn seal_trap_sites(&mut self, body: &[Stmt]) -> Result<(), PlanError> {
        let mut inventory = BodyInventory::default();
        inventory.scopes.insert(self.frame_scope);
        inventory.scopes.insert(self.body_scope);
        self.inventory_block(body, self.body_scope, &mut inventory)?;
        let route = self.trap_route();
        for key in inventory.traps {
            if self.trap_site_ids.contains_key(&key) {
                return Err(PlanError {
                    span: key.span,
                    message: format!(
                        "duplicate {:?} trap site in one lexical scope has no stable structural identity",
                        key.kind
                    ),
                });
            }
            let index = self.trap_sites.len();
            self.trap_sites.push(TrapSite {
                key: key.clone(),
                route: route.clone(),
            });
            self.trap_site_ids.insert(key, index);
        }
        Ok(())
    }

    fn trap_site(
        &self,
        scope: ScopeId,
        span: Span,
        kind: TrapSiteKind,
    ) -> Result<&TrapSite, PlanError> {
        let key = TrapSiteKey { scope, span, kind };
        let Some(index) = self.trap_site_ids.get(&key) else {
            return Err(PlanError {
                span,
                message: format!(
                    "control plan has no {:?} trap site at this span in the active lexical scope",
                    key.kind
                ),
            });
        };
        let site = &self.trap_sites[*index];
        if site.route.kind() != ExitKind::Trap
            || !site.route.scopes().is_empty()
            || !site.route.clears().is_empty()
            || !site.route.drops().is_empty()
        {
            return Err(PlanError {
                span,
                message: "control trap site does not carry the canonical empty no-unwind route"
                    .into(),
            });
        }
        Ok(site)
    }

    fn inventory_block(
        &self,
        statements: &[Stmt],
        scope: ScopeId,
        inventory: &mut BodyInventory,
    ) -> Result<(), PlanError> {
        for statement in statements {
            inventory
                .traps
                .extend(direct_statement_traps(self, scope, statement)?);
            match statement {
                Stmt::Decl {
                    ty,
                    name,
                    name_span,
                    init,
                    ..
                } => {
                    inventory.source_binding(scope, name, ty.clone(), *name_span);
                    self.inventory_array_literal_temps(scope, ty, init.as_ref(), inventory)?;
                    if let Some(expression) = init {
                        self.inventory_expression(expression, scope, inventory)?;
                    }
                }
                Stmt::Assign {
                    name,
                    name_span,
                    value,
                } => {
                    let key = AssignmentKey {
                        scope,
                        span: *name_span,
                    };
                    if !inventory.assignments.insert(key) {
                        return Err(PlanError {
                            span: *name_span,
                            message: "two assignments reuse one checked structural identity".into(),
                        });
                    }
                    let action = self.assignment(scope, *name_span, &Place::local(name))?;
                    let expected_transfer = ValueTransferKey {
                        owner: self.owner.clone(),
                        span: value.span,
                        sink: ValueTransferSink::Assignment(Place::local(name)),
                    };
                    if action.transfer_key() != &expected_transfer
                        || action.ty() != &checked_expression_ty(value, "assignment value")?
                    {
                        return Err(PlanError {
                            span: *name_span,
                            message: "assignment action no longer matches its checked RHS type, span, or transfer identity"
                                .into(),
                        });
                    }
                    match action.staging() {
                        AssignmentStaging::Direct => {}
                        AssignmentStaging::Temporary(place) => {
                            let expected = self.inventory_compiler_temp(
                                scope,
                                *name_span,
                                CompilerTempKind::AssignmentValue,
                                false,
                                inventory,
                            )?;
                            if place != &expected {
                                return Err(PlanError {
                                    span: *name_span,
                                    message:
                                        "assignment staging place no longer matches its compiler temporary"
                                            .into(),
                                });
                            }
                        }
                    }
                    self.inventory_expression(value, scope, inventory)?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    self.inventory_expression(cond, scope, inventory)?;
                    let then_scope = self.checked_child_scope(
                        ScopeKind::BranchArm(BranchArm::Then),
                        cond.span,
                        scope,
                    )?;
                    self.record_inventory_scope(
                        inventory,
                        then_scope,
                        ScopeKind::BranchArm(BranchArm::Then),
                        cond.span,
                    )?;
                    self.inventory_block(then_block, then_scope, inventory)?;

                    let else_key = ScopeKey::new(
                        &self.owner,
                        ScopeKind::BranchArm(BranchArm::Else),
                        cond.span,
                    );
                    match (else_block, self.scope_ids.get(&else_key).copied()) {
                        (Some(block), Some(else_scope)) => {
                            if self.scope_parent(else_scope) != Some(scope) {
                                return Err(PlanError {
                                    span: cond.span,
                                    message:
                                        "checked else scope moved under a different lexical parent"
                                            .into(),
                                });
                            }
                            self.record_inventory_scope(
                                inventory,
                                else_scope,
                                ScopeKind::BranchArm(BranchArm::Else),
                                cond.span,
                            )?;
                            self.inventory_block(block, else_scope, inventory)?;
                        }
                        (Some(_), None) => {
                            return Err(PlanError {
                                span: cond.span,
                                message: "checked body gained an unplanned else scope".into(),
                            });
                        }
                        (None, Some(_)) => {
                            return Err(PlanError {
                                span: cond.span,
                                message: "checked body no longer contains its planned else scope"
                                    .into(),
                            });
                        }
                        (None, None) => {}
                    }
                }
                Stmt::Return { value, span } => {
                    if !inventory.returns.insert((*span, scope)) {
                        return Err(PlanError {
                            span: *span,
                            message: "two returns reuse one checked structural identity".into(),
                        });
                    }
                    let routes = self.explicit_return(*span, scope)?;
                    if routes.result_slot().is_some() != value.is_some() {
                        return Err(PlanError {
                            span: *span,
                            message:
                                "checked return value shape no longer matches its planned result slot"
                                    .into(),
                        });
                    }
                    if let Some(expression) = value {
                        let expected = self.inventory_compiler_temp(
                            scope,
                            *span,
                            CompilerTempKind::ReturnValue,
                            false,
                            inventory,
                        )?;
                        if routes.result_slot() != Some(&expected) {
                            return Err(PlanError {
                                span: *span,
                                message:
                                    "return result slot no longer matches its compiler temporary"
                                        .into(),
                            });
                        }
                        self.inventory_expression(expression, scope, inventory)?;
                    }
                }
                Stmt::ExprStmt(expression) => {
                    if matches!(
                        checked_expression_ty(expression, "discarded expression")?,
                        Ty::Class(_)
                    ) {
                        let key = TemporaryDropKey {
                            scope,
                            span: expression.span,
                        };
                        if !inventory.temporary_drops.insert(key) {
                            return Err(PlanError {
                                span: expression.span,
                                message: "two discarded class temporaries reuse one checked structural identity"
                                    .into(),
                            });
                        }
                        let action = self.temporary_drop(scope, expression)?;
                        let expected = self.inventory_compiler_temp(
                            scope,
                            expression.span,
                            CompilerTempKind::DiscardedClassValue,
                            false,
                            inventory,
                        )?;
                        if action.temporary() != &expected {
                            return Err(PlanError {
                                span: expression.span,
                                message: "discarded class action no longer uses its exact compiler temporary"
                                    .into(),
                            });
                        }
                    }
                    self.inventory_expression(expression, scope, inventory)?;
                }
                Stmt::Assert(_) => {}
                Stmt::VarDecl {
                    name,
                    name_span,
                    init,
                    ty,
                    ..
                } => {
                    let ty = ty.clone().ok_or_else(|| PlanError {
                        span: *name_span,
                        message: format!(
                            "inferred local `{name}` has no checked type for control reconciliation"
                        ),
                    })?;
                    inventory.source_binding(scope, name, ty.clone(), *name_span);
                    self.inventory_array_literal_temps(scope, &ty, Some(init), inventory)?;
                    self.inventory_expression(init, scope, inventory)?;
                }
                Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                } => {
                    let key = FieldAssignmentKey {
                        scope,
                        span: *field_span,
                    };
                    if !inventory.field_assignments.insert(key) {
                        return Err(PlanError {
                            span: *field_span,
                            message: "two field assignments reuse one checked structural identity"
                                .into(),
                        });
                    }
                    let destination = Place::field("self", field);
                    let action = self.field_assignment(scope, *field_span, &destination, value)?;
                    match action.staging() {
                        AssignmentStaging::Direct => {}
                        AssignmentStaging::Temporary(place) => {
                            let expected = self.inventory_compiler_temp(
                                scope,
                                *field_span,
                                CompilerTempKind::FieldAssignmentValue,
                                false,
                                inventory,
                            )?;
                            if place != &expected {
                                return Err(PlanError {
                                    span: *field_span,
                                    message: "field-assignment staging place no longer matches its compiler temporary"
                                        .into(),
                                });
                            }
                        }
                    }
                    self.inventory_expression(value, scope, inventory)?;
                }
                Stmt::FieldStore { index, value, .. } | Stmt::Store { index, value, .. } => {
                    self.inventory_expression(index, scope, inventory)?;
                    self.inventory_expression(value, scope, inventory)?;
                }
                Stmt::While {
                    cond,
                    kw_span,
                    body,
                    ..
                } => {
                    self.inventory_expression(cond, scope, inventory)?;
                    let child = self.checked_child_scope(ScopeKind::LoopBody, *kw_span, scope)?;
                    self.record_inventory_scope(inventory, child, ScopeKind::LoopBody, *kw_span)?;
                    self.inventory_block(body, child, inventory)?;
                }
                Stmt::Unsafe { body, .. } => {
                    self.inventory_block(body, scope, inventory)?;
                }
                Stmt::StaticAlloc {
                    size,
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    ..
                } => {
                    inventory.source_binding(scope, ptr, Ty::Raw(IntTy::U8), *ptr_span);
                    inventory.source_binding(scope, res, Ty::Res(ResKind::RawSpan), *res_span);
                    self.inventory_expression(size, scope, inventory)?;
                }
                Stmt::SystemAlloc {
                    size,
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    release,
                    release_span,
                    ..
                } => {
                    inventory.source_binding(scope, ptr, Ty::Raw(IntTy::U8), *ptr_span);
                    inventory.source_binding(scope, res, Ty::Res(ResKind::RawSpan), *res_span);
                    inventory.source_binding(
                        scope,
                        release,
                        Ty::Res(ResKind::SystemDealloc),
                        *release_span,
                    );
                    self.inventory_expression(size, scope, inventory)?;
                }
                Stmt::SystemDealloc {
                    ptr, res, release, ..
                } => {
                    self.inventory_expression(ptr, scope, inventory)?;
                    self.inventory_expression(res, scope, inventory)?;
                    self.inventory_expression(release, scope, inventory)?;
                }
                Stmt::Expose {
                    kw_span,
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    body,
                    ..
                } => {
                    let child = self.checked_child_scope(ScopeKind::Exposure, *kw_span, scope)?;
                    self.record_inventory_scope(inventory, child, ScopeKind::Exposure, *kw_span)?;
                    inventory.source_binding(child, ptr, Ty::Raw(IntTy::U8), *ptr_span);
                    inventory.source_binding(child, res, Ty::Res(ResKind::RawSpan), *res_span);
                    for kind in [
                        CompilerTempKind::ExposureLoan,
                        CompilerTempKind::ExposureIndex,
                        CompilerTempKind::ExposureByte,
                    ] {
                        self.inventory_compiler_temp(child, *kw_span, kind, false, inventory)?;
                    }
                    self.inventory_block(body, child, inventory)?;
                }
            }
        }
        Ok(())
    }

    fn inventory_expression(
        &self,
        expression: &Expr,
        scope: ScopeId,
        inventory: &mut BodyInventory,
    ) -> Result<(), PlanError> {
        inventory.traps.extend(
            direct_expression_traps(expression)?
                .into_iter()
                .map(|(span, kind)| TrapSiteKey { scope, span, kind }),
        );
        match &expression.kind {
            ExprKind::Unary { operand, .. }
            | ExprKind::Widen { arg: operand, .. }
            | ExprKind::Narrow { arg: operand, .. }
            | ExprKind::IsSome { operand }
            | ExprKind::OptValue { operand }
            | ExprKind::SomeE(operand) => {
                self.inventory_expression(operand, scope, inventory)?;
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.inventory_expression(lhs, scope, inventory)?;
                self.inventory_expression(rhs, scope, inventory)?;
            }
            ExprKind::Call { args, .. }
            | ExprKind::RawOp { args, .. }
            | ExprKind::DeviceOp { args, .. }
            | ExprKind::ResOp { args, .. }
            | ExprKind::CtorCall { args, .. }
            | ExprKind::TraitCall { args, .. }
            | ExprKind::MethodCall { args, .. }
            | ExprKind::RecordLit { args, .. }
            | ExprKind::ArrayLit(args)
            | ExprKind::SlotOp { args, .. } => {
                for argument in args {
                    self.inventory_expression(argument, scope, inventory)?;
                }
            }
            ExprKind::Index { index, .. }
            | ExprKind::SelfFieldIndex { index, .. }
            | ExprKind::ClassFieldIndex { index, .. } => {
                self.inventory_expression(index, scope, inventory)?;
            }
            ExprKind::AllocArray { len, init, .. } => {
                self.inventory_expression(len, scope, inventory)?;
                self.inventory_expression(init, scope, inventory)?;
            }
            ExprKind::IntLit(_)
            | ExprKind::BoolLit(_)
            | ExprKind::Var(_)
            | ExprKind::Len { .. }
            | ExprKind::OptTake { .. }
            | ExprKind::NoneE
            | ExprKind::SelfField { .. }
            | ExprKind::SelfFieldLen { .. }
            | ExprKind::ClassField { .. }
            | ExprKind::RecordField { .. }
            | ExprKind::ClassFieldLen { .. }
            | ExprKind::Borrow { .. } => {}
        }
        Ok(())
    }

    fn inventory_array_literal_temps(
        &self,
        scope: ScopeId,
        ty: &Ty,
        initializer: Option<&Expr>,
        inventory: &mut BodyInventory,
    ) -> Result<(), PlanError> {
        if !ty.is_array_of(&Ty::Bool) {
            return Ok(());
        }
        let Some(Expr {
            kind: ExprKind::ArrayLit(elements),
            span,
            ..
        }) = initializer
        else {
            return Ok(());
        };
        for index in 0..elements.len() {
            self.inventory_compiler_temp(
                scope,
                *span,
                CompilerTempKind::BoolLiteralElement(index),
                true,
                inventory,
            )?;
        }
        Ok(())
    }

    fn inventory_compiler_temp(
        &self,
        scope: ScopeId,
        anchor: Span,
        kind: CompilerTempKind,
        clear_with_scope: bool,
        inventory: &mut BodyInventory,
    ) -> Result<Place, PlanError> {
        let key = CompilerTempKey {
            scope,
            anchor,
            kind,
        };
        if inventory.compiler_temps.contains(&key) {
            return Err(PlanError {
                span: anchor,
                message: format!(
                    "two source operations reuse one {kind:?} compiler-temporary identity"
                ),
            });
        }
        let place = self.compiler_temp(scope, anchor, kind)?.clone();
        inventory.compiler_temp(key, place.clone(), clear_with_scope);
        Ok(place)
    }

    fn checked_child_scope(
        &self,
        kind: ScopeKind,
        anchor: Span,
        parent: ScopeId,
    ) -> Result<ScopeId, PlanError> {
        let child = self.scope_for(kind, anchor)?;
        if self.scope_parent(child) != Some(parent) {
            return Err(PlanError {
                span: anchor,
                message: format!("checked {kind:?} scope moved under a different lexical parent"),
            });
        }
        Ok(child)
    }

    fn record_inventory_scope(
        &self,
        inventory: &mut BodyInventory,
        scope: ScopeId,
        kind: ScopeKind,
        anchor: Span,
    ) -> Result<(), PlanError> {
        if !inventory.scopes.insert(scope) {
            return Err(PlanError {
                span: anchor,
                message: format!(
                    "two retained {kind:?} blocks reuse one checked structural identity"
                ),
            });
        }
        Ok(())
    }
}

/// One checked callable and the exact lexical plan built from its typed body.
///
/// The semantic owner is retained beside the plan rather than reconstructed by
/// a consumer from a display name. Initializers and methods may legally share
/// a source spelling, so their [`CallOwner`] flavor is part of the identity.
#[derive(Clone, Debug)]
pub(crate) struct ControlBody {
    owner: CallOwner,
    declaration_span: Span,
    plan: BodyPlan,
}

impl ControlBody {
    pub(crate) fn owner(&self) -> &CallOwner {
        &self.owner
    }

    pub(crate) const fn declaration_span(&self) -> Span {
        self.declaration_span
    }

    pub(crate) fn plan(&self) -> &BodyPlan {
        &self.plan
    }

    /// Reconcile the callable carrier as well as its body-local structure.
    /// The declaration span anchors the frame/body scopes, so accepting a
    /// moved declaration would make every otherwise-exact child identity
    /// relative to stale source provenance.
    pub(crate) fn validate_callable(
        &self,
        declaration_span: Span,
        params: &[Param],
        body: &[Stmt],
    ) -> Result<(), PlanError> {
        if declaration_span != self.declaration_span {
            return Err(PlanError {
                span: declaration_span,
                message: "checked callable moved away from its planned declaration span".into(),
            });
        }
        self.plan.validate_callable(params, body)
    }
}

/// Checker-ready control plans for every Sable body in one typed program.
///
/// Ordinary functions include dynamic `test_` functions because they execute
/// through the interpreter. Audited extern declarations have no Sable body and
/// therefore have no entry. Retained function/class templates are included
/// because VC generation verifies their bodies, while concrete functions and
/// class members remain executable even when they reuse a template proof.
/// Trait signatures and retained implementation metadata are not callable
/// bodies at this stage: monomorphization resolves their executable instances
/// into the ordinary function/class collections above.
///
/// `bodies` preserves deterministic program order for whole-table consumers;
/// `body_ids` is the sole exact callable lookup. `class_drops` is indexed by
/// the concrete `Ty::Class` index and deliberately excludes retained generic
/// templates, which are verified but cannot be runtime values. A consumer
/// must use the exact lookup APIs so a missing identity is an error rather
/// than an optional fallback to rebuilding control facts.
#[derive(Clone, Debug, Default)]
pub(crate) struct ControlProgram {
    bodies: Vec<ControlBody>,
    body_ids: HashMap<CallOwner, usize>,
    class_drops: Vec<ClassDropPlan>,
}

impl ControlProgram {
    pub(crate) fn build(program: &Program) -> Result<Self, PlanError> {
        let outlines = ControlOutlines::for_program(program);
        Self::seal(program, &outlines)
    }

    pub(crate) fn seal(program: &Program, outlines: &ControlOutlines) -> Result<Self, PlanError> {
        let mut control = Self::default();

        for function in &program.fns {
            if function.extern_info.is_none() {
                control.insert_body(
                    outlines,
                    CallOwner::Function(function.name.clone()),
                    function.span,
                    &function.params,
                    &function.body,
                )?;
            }
        }
        for function in &program.fn_templates {
            control.insert_body(
                outlines,
                CallOwner::Function(function.name.clone()),
                function.span,
                &function.params,
                &function.body,
            )?;
        }
        for (class_index, class) in program.classes.iter().enumerate() {
            control
                .class_drops
                .push(ClassDropPlan::build(class_index, class)?);
            control.insert_class(outlines, class)?;
        }
        for class in &program.class_templates {
            control.insert_class(outlines, class)?;
        }

        control.validate_cleanup_action_links(&program.classes)?;

        Ok(control)
    }

    pub(crate) fn body(
        &self,
        owner: &CallOwner,
        use_span: Span,
    ) -> Result<&ControlBody, PlanError> {
        self.body_ids
            .get(owner)
            .map(|index| &self.bodies[*index])
            .ok_or_else(|| PlanError {
                span: use_span,
                message: format!("control program has no body for {}", owner.render()),
            })
    }

    /// Resolve and reconcile one concrete class destruction recipe. The
    /// declaration is supplied by the consumer's AST so reordered classes,
    /// fields, contracts, or deinitializer presence fail before execution.
    pub(crate) fn class_drop(
        &self,
        class: usize,
        declaration: &ClassDecl,
    ) -> Result<&ClassDropPlan, PlanError> {
        let Some(plan) = self.class_drops.get(class) else {
            return Err(PlanError {
                span: declaration.name_span,
                message: format!(
                    "control program has no class-drop plan for concrete class index {class}"
                ),
            });
        };
        plan.validate(class, declaration)?;
        Ok(plan)
    }

    /// Resolve a statement-local class cleanup action to the exact concrete
    /// destruction recipe retained by this same control program.
    pub(crate) fn class_drop_for_action(
        &self,
        action: &ClassDropAction,
        classes: &[ClassDecl],
        use_span: Span,
    ) -> Result<&ClassDropPlan, PlanError> {
        let declaration = classes.get(action.class()).ok_or_else(|| PlanError {
            span: use_span,
            message: format!(
                "cleanup action names missing concrete class index {}",
                action.class()
            ),
        })?;
        let plan = self.class_drop(action.class(), declaration)?;
        if action.terminal_trap_route() != plan.terminal_trap_route()
            || !action.terminal_trap_route().is_terminal_trap()
        {
            return Err(PlanError {
                span: use_span,
                message: format!(
                    "cleanup action for class `{}` no longer uses its retained terminal no-unwind route",
                    declaration.name
                ),
            });
        }
        Ok(plan)
    }

    /// Reconcile one recursive value-destruction action with both its exact
    /// type shape and every concrete class recipe reachable through a
    /// dynamically present payload. Array actions are release-only in the
    /// current language: their element type is retained, and affine elements
    /// fail during action construction before they can acquire raw-free
    /// semantics by accident.
    pub(crate) fn validate_value_drop_action(
        &self,
        action: &ValueDropAction,
        classes: &[ClassDecl],
        use_span: Span,
    ) -> Result<(), PlanError> {
        let expected = ValueDropAction::build(action.ty(), use_span)?.ok_or_else(|| PlanError {
            span: use_span,
            message: format!(
                "non-cleanup type `{}` retained a value-drop action",
                action.ty().name()
            ),
        })?;
        if action != &expected {
            return Err(PlanError {
                span: use_span,
                message: format!(
                    "value-drop action for `{}` no longer matches its exact recursive recipe",
                    action.ty().name()
                ),
            });
        }
        match action.recipe() {
            ValueDropRecipe::ReleaseArray { .. } => Ok(()),
            ValueDropRecipe::DropClass(class) => {
                self.class_drop_for_action(class, classes, use_span)?;
                Ok(())
            }
            ValueDropRecipe::DropPresent(payload) => {
                self.validate_value_drop_action(payload, classes, use_span)
            }
        }
    }

    pub(crate) fn class_drops(&self) -> &[ClassDropPlan] {
        &self.class_drops
    }

    pub(crate) fn iter(&self) -> impl ExactSizeIterator<Item = &ControlBody> {
        self.bodies.iter()
    }

    pub(crate) fn len(&self) -> usize {
        self.bodies.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.bodies.is_empty()
    }

    fn validate_cleanup_action_links(&self, classes: &[ClassDecl]) -> Result<(), PlanError> {
        for plan in &self.class_drops {
            for phase in plan.phases() {
                if let ClassDropPhase::DropField(field) = phase {
                    if let Some(drop_action) = field.drop_action() {
                        self.validate_value_drop_action(drop_action, classes, field.span())?;
                    }
                }
            }
        }
        for body in &self.bodies {
            for candidate in &body.plan().candidates {
                self.validate_value_drop_action(
                    candidate.drop_action(),
                    classes,
                    candidate.span(),
                )?;
            }
            for action in body.plan().field_assignments() {
                if let Some(drop_action) = action.drop_action() {
                    self.validate_value_drop_action(drop_action, classes, action.span())?;
                }
            }
            for action in body.plan().temporary_drops() {
                self.validate_value_drop_action(action.drop_action(), classes, action.span())?;
            }
        }
        Ok(())
    }

    fn insert_class(
        &mut self,
        outlines: &ControlOutlines,
        class: &ClassDecl,
    ) -> Result<(), PlanError> {
        for initializer in &class.inits {
            self.insert_body(
                outlines,
                CallOwner::Constructor {
                    class: class.name.clone(),
                    init: initializer.name.clone(),
                },
                initializer.span,
                &initializer.params,
                &initializer.body,
            )?;
        }
        for method in &class.methods {
            self.insert_body(
                outlines,
                CallOwner::Method {
                    class: class.name.clone(),
                    method: method.f.name.clone(),
                },
                method.f.span,
                &method.f.params,
                &method.f.body,
            )?;
        }
        if let Some(body) = &class.deinit {
            self.insert_body(
                outlines,
                CallOwner::Deinitializer {
                    class: class.name.clone(),
                },
                class.span,
                &[],
                body,
            )?;
        }
        Ok(())
    }

    fn insert_body(
        &mut self,
        outlines: &ControlOutlines,
        owner: CallOwner,
        declaration_span: Span,
        params: &[Param],
        body: &[Stmt],
    ) -> Result<(), PlanError> {
        if self.body_ids.contains_key(&owner) {
            return Err(PlanError {
                span: declaration_span,
                message: format!("duplicate control body identity for {}", owner.render()),
            });
        }
        let outline = outlines.exact(&owner, declaration_span)?;
        let plan = BodyPlan::seal(outline, params, body)?;
        let index = self.bodies.len();
        self.bodies.push(ControlBody {
            owner: owner.clone(),
            declaration_span,
            plan,
        });
        self.body_ids.insert(owner, index);
        Ok(())
    }
}

struct PlanBuilder {
    plan: BodyPlan,
    /// All source names, not only owning ones. The checker reserves names for
    /// an entire callable; enforcing that here keeps place lookup unambiguous
    /// even for forged typed ASTs.
    declared: HashSet<String>,
    /// Source binding facts available at the current structural position.
    /// Names are globally unique in one callable, while the recorded scope
    /// still prevents a sibling branch from becoming an accidental target.
    bindings: HashMap<String, PlannedBinding>,
    exposure_depth: usize,
}

#[derive(Clone, Debug)]
struct PlannedBinding {
    scope: ScopeId,
    ty: Ty,
}

impl PlanBuilder {
    fn outlined_scope(
        &self,
        kind: ScopeKind,
        anchor: Span,
        parent: ScopeId,
    ) -> Result<ScopeId, PlanError> {
        let key = ScopeKey::new(&self.plan.owner, kind, anchor);
        let scope = self
            .plan
            .scope_ids
            .get(&key)
            .copied()
            .ok_or_else(|| PlanError {
                span: anchor,
                message: format!("pre-check outline has no {kind:?} scope at this anchor"),
            })?;
        if self.plan.scopes[scope.0].parent != Some(parent) {
            return Err(PlanError {
                span: anchor,
                message: format!("checked {kind:?} scope moved under a different parent"),
            });
        }
        Ok(scope)
    }

    fn declare(&mut self, scope: ScopeId, name: &str, ty: Ty, span: Span) -> Result<(), PlanError> {
        self.reserve(scope, name, ty.clone(), span)?;
        let Some(drop_action) = ValueDropAction::build(&ty, span)? else {
            return Ok(());
        };
        let place = Place::local(name);
        let id = DropId(self.plan.candidates.len());
        let candidate = DropCandidate {
            id,
            scope,
            place: place.clone(),
            drop_action,
            span,
        };
        self.plan.candidates.push(candidate);
        self.plan.candidate_ids.insert(place, id);
        self.plan.scopes[scope.0].drops.push(id);
        Ok(())
    }

    fn reserve(&mut self, scope: ScopeId, name: &str, ty: Ty, span: Span) -> Result<(), PlanError> {
        if !self.declared.insert(name.to_owned()) {
            return Err(PlanError {
                span,
                message: format!("duplicate local `{name}` has no unique cleanup identity"),
            });
        }
        let place = Place::local(name);
        self.plan.scopes[scope.0].locals.push(place.clone());
        self.plan.scopes[scope.0].bindings.push(SourceBinding {
            place,
            ty: ty.clone(),
            span,
        });
        self.bindings
            .insert(name.to_owned(), PlannedBinding { scope, ty });
        Ok(())
    }

    fn scope_contains(&self, ancestor: ScopeId, mut scope: ScopeId) -> bool {
        loop {
            if scope == ancestor {
                return true;
            }
            let Some(parent) = self.plan.scopes[scope.0].parent else {
                return false;
            };
            scope = parent;
        }
    }

    fn assignment(
        &mut self,
        scope: ScopeId,
        name: &str,
        span: Span,
        value: &Expr,
    ) -> Result<(), PlanError> {
        let binding = self.bindings.get(name).cloned().ok_or_else(|| PlanError {
            span,
            message: format!("assignment to `{name}` has no preceding planned binding"),
        })?;
        if !self.scope_contains(binding.scope, scope) {
            return Err(PlanError {
                span,
                message: format!("assignment to `{name}` targets a binding outside this scope"),
            });
        }
        let key = AssignmentKey { scope, span };
        if self.plan.assignment_ids.contains_key(&key) {
            return Err(PlanError {
                span,
                message:
                    "duplicate assignment span in one lexical scope has no stable control identity"
                        .into(),
            });
        }
        let destination = Place::local(name);
        let previous = self.plan.candidate_ids.get(&destination).copied();
        let staging = if previous.is_some() {
            AssignmentStaging::Temporary(self.compiler_temp(
                scope,
                span,
                CompilerTempKind::AssignmentValue,
                false,
            )?)
        } else {
            AssignmentStaging::Direct
        };
        let index = self.plan.assignments.len();
        self.plan.assignments.push(AssignmentAction {
            scope,
            span,
            destination,
            ty: binding.ty,
            transfer_key: ValueTransferKey {
                owner: self.plan.owner.clone(),
                span: value.span,
                sink: ValueTransferSink::Assignment(Place::local(name)),
            },
            previous,
            staging,
        });
        self.plan.assignment_ids.insert(key, index);
        Ok(())
    }

    fn field_assignment(
        &mut self,
        scope: ScopeId,
        field: &str,
        span: Span,
        value: &Expr,
    ) -> Result<(), PlanError> {
        let key = FieldAssignmentKey { scope, span };
        if self.plan.field_assignment_ids.contains_key(&key) {
            return Err(PlanError {
                span,
                message:
                    "duplicate field-assignment span in one lexical scope has no stable control identity"
                        .into(),
            });
        }
        let destination = Place::field("self", field);
        let ty = checked_expression_ty(value, "field-assignment value")?;
        let drop_action = ValueDropAction::build(&ty, span)?;
        let staging = if drop_action.is_some() {
            AssignmentStaging::Temporary(self.compiler_temp(
                scope,
                span,
                CompilerTempKind::FieldAssignmentValue,
                false,
            )?)
        } else {
            AssignmentStaging::Direct
        };
        let transfer_key = ValueTransferKey {
            owner: self.plan.owner.clone(),
            span: value.span,
            sink: ValueTransferSink::FieldAssignment(destination.clone()),
        };
        let index = self.plan.field_assignments.len();
        self.plan.field_assignments.push(FieldAssignmentAction {
            scope,
            span,
            destination,
            ty,
            transfer_key,
            staging,
            drop_action,
        });
        self.plan.field_assignment_ids.insert(key, index);
        Ok(())
    }

    fn temporary_drop(&mut self, scope: ScopeId, expression: &Expr) -> Result<(), PlanError> {
        let ty = checked_expression_ty(expression, "discarded class temporary")?;
        let Ty::Class(_) = ty else {
            return Ok(());
        };
        let drop_action = ValueDropAction::build(&ty, expression.span)?
            .expect("class values always have a sealed drop action");
        if let Some(source) = Place::from_value_expr(expression) {
            return Err(PlanError {
                span: expression.span,
                message: format!(
                    "discarded class temporary unexpectedly names source place `{}`",
                    source.render()
                ),
            });
        }
        let key = TemporaryDropKey {
            scope,
            span: expression.span,
        };
        if self.plan.temporary_drop_ids.contains_key(&key) {
            return Err(PlanError {
                span: expression.span,
                message:
                    "duplicate discarded-class span in one lexical scope has no stable control identity"
                        .into(),
            });
        }
        let temporary = self.compiler_temp(
            scope,
            expression.span,
            CompilerTempKind::DiscardedClassValue,
            false,
        )?;
        let index = self.plan.temporary_drops.len();
        self.plan.temporary_drops.push(TemporaryDropAction {
            scope,
            span: expression.span,
            transfer_key: ValueTransferKey {
                owner: self.plan.owner.clone(),
                span: expression.span,
                sink: ValueTransferSink::DiscardTemporary,
            },
            temporary,
            drop_action,
        });
        self.plan.temporary_drop_ids.insert(key, index);
        Ok(())
    }

    fn compiler_temp(
        &mut self,
        scope: ScopeId,
        anchor: Span,
        kind: CompilerTempKind,
        clear_with_scope: bool,
    ) -> Result<Place, PlanError> {
        let key = CompilerTempKey {
            scope,
            anchor,
            kind,
        };
        if self.plan.compiler_temps.contains_key(&key) {
            return Err(PlanError {
                span: anchor,
                message: format!("duplicate {kind:?} compiler temporary identity"),
            });
        }
        let role = match kind {
            CompilerTempKind::ReturnValue => "return",
            CompilerTempKind::AssignmentValue => "assignment",
            CompilerTempKind::FieldAssignmentValue => "field_assignment",
            CompilerTempKind::DiscardedClassValue => "discarded_class",
            CompilerTempKind::ExposureLoan => "exposure_loan",
            CompilerTempKind::ExposureIndex => "exposure_index",
            CompilerTempKind::ExposureByte => "exposure_byte",
            CompilerTempKind::BoolLiteralElement(_) => "bool_element",
        };
        let ordinal = match kind {
            CompilerTempKind::BoolLiteralElement(index) => index,
            CompilerTempKind::ReturnValue
            | CompilerTempKind::AssignmentValue
            | CompilerTempKind::FieldAssignmentValue
            | CompilerTempKind::DiscardedClassValue
            | CompilerTempKind::ExposureLoan
            | CompilerTempKind::ExposureIndex
            | CompilerTempKind::ExposureByte => 0,
        };
        let place = Place::local(&format!(
            "$sable${role}${}${}${}${ordinal}",
            anchor.start, anchor.end, scope.0
        ));
        if clear_with_scope {
            self.plan.scopes[scope.0].locals.push(place.clone());
        }
        self.plan.compiler_temps.insert(key, place.clone());
        Ok(place)
    }

    fn array_literal_temps(
        &mut self,
        scope: ScopeId,
        ty: &Ty,
        initializer: Option<&Expr>,
    ) -> Result<(), PlanError> {
        if !ty.is_array_of(&Ty::Bool) {
            return Ok(());
        }
        let Some(Expr {
            kind: ExprKind::ArrayLit(elements),
            span,
            ..
        }) = initializer
        else {
            return Ok(());
        };
        for index in 0..elements.len() {
            self.compiler_temp(
                scope,
                *span,
                CompilerTempKind::BoolLiteralElement(index),
                true,
            )?;
        }
        Ok(())
    }

    fn walk_block(&mut self, statements: &[Stmt], scope: ScopeId) -> Result<(), PlanError> {
        for statement in statements {
            match statement {
                Stmt::Decl {
                    name,
                    ty,
                    name_span,
                    init,
                    ..
                } => {
                    self.declare(scope, name, ty.clone(), *name_span)?;
                    self.array_literal_temps(scope, ty, init.as_ref())?;
                }
                Stmt::VarDecl {
                    name,
                    ty,
                    name_span,
                    init,
                    ..
                } => {
                    let ty = ty.clone().ok_or_else(|| PlanError {
                        span: *name_span,
                        message: format!(
                            "inferred local `{name}` has no checked type for cleanup planning"
                        ),
                    })?;
                    self.declare(scope, name, ty.clone(), *name_span)?;
                    self.array_literal_temps(scope, &ty, Some(init))?;
                }
                Stmt::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    let then_scope = self.outlined_scope(
                        ScopeKind::BranchArm(BranchArm::Then),
                        cond.span,
                        scope,
                    )?;
                    self.walk_block(then_block, then_scope)?;
                    if let Some(else_block) = else_block {
                        let else_scope = self.outlined_scope(
                            ScopeKind::BranchArm(BranchArm::Else),
                            cond.span,
                            scope,
                        )?;
                        self.walk_block(else_block, else_scope)?;
                    }
                }
                Stmt::While { kw_span, body, .. } => {
                    let body_scope = self.outlined_scope(ScopeKind::LoopBody, *kw_span, scope)?;
                    self.walk_block(body, body_scope)?;
                }
                // Capability marker only: declarations are activated in the
                // surrounding lexical scope at this source position.
                Stmt::Unsafe { body, .. } => self.walk_block(body, scope)?,
                Stmt::Expose {
                    kw_span,
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    body,
                    ..
                } => {
                    let exposure = self.outlined_scope(ScopeKind::Exposure, *kw_span, scope)?;
                    self.reserve(exposure, ptr, Ty::Raw(IntTy::U8), *ptr_span)?;
                    self.reserve(exposure, res, Ty::Res(ResKind::RawSpan), *res_span)?;
                    self.compiler_temp(exposure, *kw_span, CompilerTempKind::ExposureLoan, false)?;
                    self.compiler_temp(exposure, *kw_span, CompilerTempKind::ExposureIndex, false)?;
                    self.compiler_temp(exposure, *kw_span, CompilerTempKind::ExposureByte, false)?;
                    self.exposure_depth += 1;
                    let result = self.walk_block(body, exposure);
                    self.exposure_depth -= 1;
                    result?;
                }
                Stmt::Return { value, span } => {
                    if self.exposure_depth != 0 {
                        return Err(PlanError {
                            span: *span,
                            message: "return inside an exposure would bypass reconstruction".into(),
                        });
                    }
                    if !self.plan.return_sites.insert((*span, scope)) {
                        return Err(PlanError {
                            span: *span,
                            message: "duplicate return span in one lexical scope has no stable control identity".into(),
                        });
                    }
                    if value.is_some() {
                        self.compiler_temp(scope, *span, CompilerTempKind::ReturnValue, false)?;
                    }
                }
                Stmt::StaticAlloc {
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    ..
                } => {
                    self.reserve(scope, ptr, Ty::Raw(IntTy::U8), *ptr_span)?;
                    self.reserve(scope, res, Ty::Res(ResKind::RawSpan), *res_span)?;
                }
                Stmt::SystemAlloc {
                    ptr,
                    ptr_span,
                    res,
                    res_span,
                    release,
                    release_span,
                    ..
                } => {
                    self.reserve(scope, ptr, Ty::Raw(IntTy::U8), *ptr_span)?;
                    self.reserve(scope, res, Ty::Res(ResKind::RawSpan), *res_span)?;
                    self.reserve(
                        scope,
                        release,
                        Ty::Res(ResKind::SystemDealloc),
                        *release_span,
                    )?;
                }
                Stmt::Assign {
                    name,
                    name_span,
                    value,
                } => self.assignment(scope, name, *name_span, value)?,
                Stmt::ExprStmt(expression) => self.temporary_drop(scope, expression)?,
                Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                } => self.field_assignment(scope, field, *field_span, value)?,
                Stmt::Assert(_)
                | Stmt::FieldStore { .. }
                | Stmt::Store { .. }
                | Stmt::SystemDealloc { .. } => {}
            }
        }
        Ok(())
    }
}

fn checked_expression_ty(expression: &Expr, role: &str) -> Result<Ty, PlanError> {
    expression.ty.clone().ok_or_else(|| PlanError {
        span: expression.span,
        message: format!("{role} has no checked type for trap-site planning"),
    })
}

fn checked_integer_ty(expression: &Expr, role: &str) -> Result<IntTy, PlanError> {
    match checked_expression_ty(expression, role)? {
        Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Ok(integer),
        ty => Err(PlanError {
            span: expression.span,
            message: format!(
                "{role} has checked type `{}`, not a concrete integer",
                ty.name()
            ),
        }),
    }
}

/// Direct (non-child) expression trap identities. This classifier is shared by
/// plan sealing, complete body reconciliation, and each runtime consumer.
///
/// Deliberate exclusions are operations whose failure is not an admitted
/// source-runtime edge: resource split/join and allocator transformations are
/// proof-state transitions in the interpreter; `TraitCall` survives only in
/// templates and is never executed; array payload mismatches require a forged
/// checked type. Static/system allocation and exposure entry likewise use the
/// checker's bounded infallible source in the interpreter. Their operational
/// trap-bearing counterparts below are allocation expressions, explicit
/// system deallocation, and exposure close.
fn direct_expression_traps(expression: &Expr) -> Result<Vec<(Span, TrapSiteKind)>, PlanError> {
    let mut traps = Vec::new();
    match &expression.kind {
        ExprKind::SlotOp { op, .. } => {
            return Err(PlanError {
                span: expression.span,
                message: format!(
                    "internal.control.slots_unsupported: `{}` has no retained trap-site plan",
                    op.name()
                ),
            });
        }
        ExprKind::Unary { op: UnOp::Neg, .. } => traps.push((
            expression.span,
            TrapSiteKind::NegOverflow(checked_integer_ty(expression, "negation")?),
        )),
        ExprKind::Unary { op: UnOp::Not, .. } => {}
        ExprKind::Binary { op, .. } => {
            let integer = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                    Some(checked_integer_ty(expression, "arithmetic expression")?)
                }
                BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::And
                | BinOp::Or => None,
            };
            match (op, integer) {
                (BinOp::Add, Some(integer)) => {
                    traps.push((expression.span, TrapSiteKind::AddOverflow(integer)));
                }
                (BinOp::Sub, Some(integer)) => {
                    traps.push((expression.span, TrapSiteKind::SubOverflow(integer)));
                }
                (BinOp::Mul, Some(integer)) => {
                    traps.push((expression.span, TrapSiteKind::MulOverflow(integer)));
                }
                (BinOp::Div, Some(integer)) => {
                    traps.push((expression.span, TrapSiteKind::DivByZero(integer)));
                    if integer.signed() {
                        traps.push((expression.span, TrapSiteKind::DivOverflow(integer)));
                    }
                }
                (BinOp::Rem, Some(integer)) => {
                    traps.push((expression.span, TrapSiteKind::RemByZero(integer)));
                }
                (
                    BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge
                    | BinOp::Eq
                    | BinOp::Ne
                    | BinOp::And
                    | BinOp::Or,
                    None,
                ) => {}
                _ => unreachable!("arithmetic operators receive an integer trap type"),
            }
        }
        ExprKind::Narrow { target, arg } => traps.push((
            expression.span,
            TrapSiteKind::NarrowRange {
                source: checked_integer_ty(arg, "narrow operand")?,
                target: *target,
            },
        )),
        ExprKind::OptValue { .. } => traps.push((
            expression.span,
            TrapSiteKind::OptionValue(checked_expression_ty(expression, "option payload")?),
        )),
        ExprKind::OptTake { option, .. } => traps.push((
            expression.span,
            TrapSiteKind::OptionTake {
                option: option.clone(),
                payload: checked_expression_ty(expression, "affine option take")?,
            },
        )),
        ExprKind::ArrayLit(elements) => {
            if !elements.is_empty() {
                let ty = checked_expression_ty(expression, "array literal")?;
                let Some((element, _)) = ty.as_array() else {
                    return Err(PlanError {
                        span: expression.span,
                        message: "array literal has no checked array element type".into(),
                    });
                };
                traps.push((
                    expression.span,
                    TrapSiteKind::ArrayAllocation {
                        element: element.clone(),
                        phase: AllocationTrapPhase::Allocator,
                    },
                ));
            }
        }
        ExprKind::AllocArray { elem, .. } => {
            traps.push((
                expression.span,
                TrapSiteKind::ArrayAllocation {
                    element: elem.clone(),
                    phase: AllocationTrapPhase::Capacity,
                },
            ));
            traps.push((
                expression.span,
                TrapSiteKind::ArrayAllocation {
                    element: elem.clone(),
                    phase: AllocationTrapPhase::Allocator,
                },
            ));
        }
        ExprKind::Index { array, .. } => traps.push((
            expression.span,
            TrapSiteKind::ArrayIndex {
                array: array.clone(),
                element: checked_expression_ty(expression, "array index result")?,
            },
        )),
        ExprKind::SelfFieldIndex { field, .. } => traps.push((
            expression.span,
            TrapSiteKind::SelfFieldIndex {
                field: field.clone(),
                element: checked_expression_ty(expression, "self array-field index result")?,
            },
        )),
        ExprKind::ClassFieldIndex { obj, field, .. } => traps.push((
            expression.span,
            TrapSiteKind::ClassFieldIndex {
                object: obj.clone(),
                field: field.clone(),
                element: checked_expression_ty(expression, "class array-field index result")?,
            },
        )),
        ExprKind::Call { callee, .. } => traps.push((
            expression.span,
            TrapSiteKind::FunctionCall {
                callee: callee.clone(),
                result: checked_expression_ty(expression, "function call")?,
            },
        )),
        ExprKind::CtorCall { class, init, .. } => traps.push((
            expression.span,
            TrapSiteKind::ConstructorCall {
                class: class.clone(),
                initializer: init.clone(),
                result: checked_expression_ty(expression, "constructor call")?,
            },
        )),
        ExprKind::MethodCall { recv, method, .. } => traps.push((
            expression.span,
            TrapSiteKind::MethodCall {
                receiver: recv.clone(),
                method: method.clone(),
                result: checked_expression_ty(expression, "method call")?,
            },
        )),
        ExprKind::RawOp { op, .. } => {
            if op.touches_memory() {
                traps.push((
                    expression.span,
                    TrapSiteKind::RawOperation(format!("{op:?}")),
                ));
            } else {
                debug_assert!(matches!(
                    op,
                    RawOp::Offset | RawOp::CastRecord(_) | RawOp::PointerOffsetRecord(_)
                ));
            }
        }
        ExprKind::ResOp { op, .. } => match op {
            ResOp::TestUart
            | ResOp::OpenFileOf
            | ResOp::ResourceMapTake
            | ResOp::ResourceMapPut => {
                traps.push((
                    expression.span,
                    TrapSiteKind::ResourceOperation(format!("{op:?}")),
                ));
            }
            ResOp::SplitOff
            | ResOp::Join
            | ResOp::TestWorld
            | ResOp::AllocatorCreate
            | ResOp::AllocatorDestroy
            | ResOp::AllocatorTake
            | ResOp::AllocatorPut
            | ResOp::AllocatorTakeFree
            | ResOp::AllocatorPutFree
            | ResOp::AllocatorTakeHeader
            | ResOp::AllocatorPutHeader
            | ResOp::AllocatorStepHeader
            | ResOp::FreeBlockSplit
            | ResOp::FreeBlockJoin
            | ResOp::FreeBlockLease
            | ResOp::BlockLeaseFree
            | ResOp::ResourceMapEmpty => {}
        },
        ExprKind::DeviceOp { op, .. } => traps.push((
            expression.span,
            TrapSiteKind::DeviceOperation(format!("{op:?}")),
        )),
        ExprKind::IntLit(_)
        | ExprKind::BoolLit(_)
        | ExprKind::Var(_)
        | ExprKind::Len { .. }
        | ExprKind::Widen { .. }
        | ExprKind::IsSome { .. }
        | ExprKind::SomeE(_)
        | ExprKind::NoneE
        | ExprKind::SelfField { .. }
        | ExprKind::SelfFieldLen { .. }
        | ExprKind::ClassField { .. }
        | ExprKind::RecordField { .. }
        | ExprKind::ClassFieldLen { .. }
        | ExprKind::TraitCall { .. }
        | ExprKind::Borrow { .. }
        | ExprKind::RecordLit { .. } => {}
    }
    Ok(traps)
}

/// Direct statement traps. Expression children use
/// [`direct_expression_traps`] when the consumer evaluates or lowers them.
fn direct_statement_traps(
    plan: &BodyPlan,
    scope: ScopeId,
    statement: &Stmt,
) -> Result<Vec<TrapSiteKey>, PlanError> {
    let mut traps = Vec::new();
    let mut push = |scope, span, kind| traps.push(TrapSiteKey { scope, span, kind });
    match statement {
        Stmt::Assert(clause) => push(
            scope,
            clause.span,
            TrapSiteKind::InlineAssert(clause.text.clone()),
        ),
        Stmt::FieldStore {
            field,
            field_span,
            value,
            ..
        } => push(
            scope,
            *field_span,
            TrapSiteKind::SelfFieldStore {
                field: field.clone(),
                element: checked_expression_ty(value, "field-store value")?,
            },
        ),
        Stmt::Store {
            array,
            array_span,
            value,
            ..
        } => push(
            scope,
            *array_span,
            TrapSiteKind::ArrayStore {
                array: array.clone(),
                element: checked_expression_ty(value, "array-store value")?,
            },
        ),
        Stmt::While {
            invariants,
            variant,
            ..
        } => {
            for invariant in invariants {
                push(
                    scope,
                    invariant.span,
                    TrapSiteKind::LoopInvariant(invariant.text.clone()),
                );
            }
            if let Some(variant) = variant {
                push(
                    scope,
                    variant.span,
                    TrapSiteKind::LoopVariantNegative(variant.text.clone()),
                );
                push(
                    scope,
                    variant.span,
                    TrapSiteKind::LoopVariantNonDecrease(variant.text.clone()),
                );
            }
        }
        Stmt::SystemDealloc { kw_span, .. } => {
            push(scope, *kw_span, TrapSiteKind::SystemDealloc);
        }
        Stmt::Expose {
            kw_span,
            array,
            mutable: true,
            ..
        } => {
            let exposure = plan.exposure_plan(scope, *kw_span)?.body_scope();
            push(
                exposure,
                *kw_span,
                TrapSiteKind::ExposureClose {
                    array: array.clone(),
                    mutable: true,
                },
            );
        }
        Stmt::Decl { .. }
        | Stmt::Assign { .. }
        | Stmt::If { .. }
        | Stmt::Return { .. }
        | Stmt::ExprStmt(_)
        | Stmt::VarDecl { .. }
        | Stmt::FieldAssign { .. }
        | Stmt::Unsafe { .. }
        | Stmt::StaticAlloc { .. }
        | Stmt::SystemAlloc { .. }
        | Stmt::Expose { mutable: false, .. } => {}
    }
    Ok(traps)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        ClassDecl, Expr, ExprKind, Field, Fn, Method, Param, Program, ProofReuse, SelfKind, Ty,
    };
    use crate::span::Span;

    fn bool_expr(value: bool) -> Expr {
        Expr {
            kind: ExprKind::BoolLit(value),
            span: Span::new(0, 0),
            ty: Some(Ty::Bool),
        }
    }

    fn integer_expr(value: i128, span: Span) -> Expr {
        Expr {
            kind: ExprKind::IntLit(value),
            span,
            ty: Some(Ty::Int(IntTy::I32)),
        }
    }

    fn fresh_class_expr(span: Span) -> Expr {
        Expr {
            kind: ExprKind::CtorCall {
                class: "Child".into(),
                class_span: span,
                type_args: Vec::new(),
                init: "new".into(),
                args: Vec::new(),
            },
            span,
            ty: Some(Ty::Class(0)),
        }
    }

    fn cleanup_action_body() -> Vec<Stmt> {
        vec![
            Stmt::FieldAssign {
                field: "child".into(),
                field_span: at(10),
                value: fresh_class_expr(at(11)),
            },
            Stmt::FieldAssign {
                field: "count".into(),
                field_span: at(20),
                value: integer_expr(1, at(21)),
            },
            Stmt::ExprStmt(fresh_class_expr(at(30))),
        ]
    }

    fn arithmetic_expr(op: BinOp, span: Span) -> Expr {
        Expr {
            kind: ExprKind::Binary {
                op,
                op_span: span,
                lhs: Box::new(integer_expr(4, at(span.start + 2))),
                rhs: Box::new(integer_expr(2, at(span.start + 4))),
            },
            span,
            ty: Some(Ty::Int(IntTy::I32)),
        }
    }

    fn return_statement() -> Stmt {
        Stmt::Return {
            value: None,
            span: Span::new(0, 0),
        }
    }

    fn at(start: usize) -> Span {
        Span::new(start, start + 1)
    }

    #[test]
    fn owner_slots_never_acquire_a_control_recipe_or_trap_plan() {
        let slots = Ty::slots(Ty::Int(IntTy::U64));
        let error = ValueDropAction::build(&slots, at(1))
            .expect_err("owner slots have no occupied-cell cleanup recipe yet");
        assert!(
            error
                .message
                .starts_with("internal.control.slots_unsupported:"),
            "{}",
            error.message
        );
        let error = ValueDropAction::build(&Ty::option(slots.clone()), at(1))
            .expect_err("an option over owner slots must stay on the owning cleanup path");
        assert!(
            error
                .message
                .starts_with("internal.control.slots_unsupported:"),
            "{}",
            error.message
        );

        let operation = Expr {
            kind: ExprKind::SlotOp {
                op: crate::ast::SlotOp::Alloc {
                    elem: Ty::Int(IntTy::U64),
                },
                op_span: at(2),
                args: vec![integer_expr(4, at(3))],
            },
            span: at(2),
            ty: Some(slots),
        };
        let error = direct_expression_traps(&operation)
            .expect_err("owner-slot operations have no retained trap plan yet");
        assert!(
            error
                .message
                .starts_with("internal.control.slots_unsupported:"),
            "{}",
            error.message
        );
    }

    fn owned_decl(name: &str, span: Span) -> Stmt {
        Stmt::Decl {
            ty: Ty::array(Ty::Bool),
            name: name.into(),
            name_span: span,
            init: Some(bool_expr(false)),
            mutable: false,
        }
    }

    fn function(name: &str, span: Span, local: &str) -> Fn {
        Fn {
            is_pub: false,
            extern_info: None,
            name: name.into(),
            name_span: span,
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params: Vec::new(),
            ret: Ty::Unit,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body: vec![owned_decl(local, at(span.start + 1))],
            span,
        }
    }

    fn class(name: &str, span: Span, prefix: &str) -> ClassDecl {
        ClassDecl {
            is_pub: false,
            name: name.into(),
            name_span: span,
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            proof_reuse: ProofReuse::None,
            fields: Vec::new(),
            invariants: Vec::new(),
            // Same-spelled members are legal across flavors and must retain
            // distinct semantic control identities.
            inits: vec![function(
                "same",
                at(span.start + 10),
                &format!("{prefix}_init_owner"),
            )],
            methods: vec![Method {
                self_kind: SelfKind::Shared,
                f: function(
                    "same",
                    at(span.start + 20),
                    &format!("{prefix}_method_owner"),
                ),
            }],
            deinit: Some(vec![owned_decl(
                &format!("{prefix}_deinit_owner"),
                at(span.start + 30),
            )]),
            span,
        }
    }

    fn program() -> Program {
        Program {
            fns: Vec::new(),
            fn_templates: Vec::new(),
            class_templates: Vec::new(),
            classes: Vec::new(),
            records: Vec::new(),
            traits: Vec::new(),
            impls: Vec::new(),
            discharges: Vec::new(),
            ghosts: Vec::new(),
            defers: Vec::new(),
            assumes: Vec::new(),
            operators: Vec::new(),
            uses: Vec::new(),
            consts: Vec::new(),
        }
    }

    fn drop_names(plan: &BodyPlan, route: &ExitRoute) -> Vec<String> {
        route
            .drops()
            .iter()
            .map(|drop| plan.candidate(*drop).place().render())
            .collect()
    }

    fn clear_names(route: &ExitRoute) -> Vec<String> {
        route.clears().iter().map(Place::render).collect()
    }

    fn assert_flow(
        statements: &[Stmt],
        reaches_next: bool,
        has_reachable_return: bool,
        contains_return: bool,
    ) {
        let summary = summarize_block(statements);
        assert_eq!(summary.reaches_next, reaches_next);
        assert_eq!(summary.has_reachable_return, has_reachable_return);
        assert_eq!(summary.contains_return, contains_return);
        assert_eq!(
            summary.definitely_returns(),
            has_reachable_return && !reaches_next
        );
    }

    #[test]
    fn branch_return_truth_table_distinguishes_may_from_must() {
        assert_flow(&[], true, false, false);
        assert_flow(&[return_statement()], false, true, true);

        assert_flow(
            &[Stmt::If {
                cond: bool_expr(true),
                then_block: vec![return_statement()],
                else_block: None,
            }],
            true,
            true,
            true,
        );

        assert_flow(
            &[Stmt::If {
                cond: bool_expr(true),
                then_block: vec![return_statement()],
                else_block: Some(vec![return_statement()]),
            }],
            false,
            true,
            true,
        );
    }

    #[test]
    fn loops_fall_through_and_unsafe_is_transparent() {
        let returning_loop = Stmt::While {
            cond: bool_expr(true),
            invariants: Vec::new(),
            variant: None,
            kw_span: Span::new(0, 0),
            body: vec![return_statement()],
        };
        assert_flow(&[returning_loop], true, true, true);

        let returning_unsafe = Stmt::Unsafe {
            kw_span: Span::new(0, 0),
            body: vec![return_statement()],
        };
        assert_flow(&[returning_unsafe], false, true, true);
    }

    #[test]
    fn structural_return_detection_includes_unreachable_and_exposure_bodies() {
        let unreachable_return = vec![
            return_statement(),
            Stmt::Unsafe {
                kw_span: Span::new(0, 0),
                body: vec![return_statement()],
            },
        ];
        assert_flow(&unreachable_return, false, true, true);

        let conditional_exposure_return = Stmt::Expose {
            kw_span: Span::new(0, 0),
            array: "bytes".into(),
            array_span: Span::new(0, 0),
            mutable: false,
            ptr: "ptr".into(),
            ptr_span: Span::new(0, 0),
            res: "mem".into(),
            res_span: Span::new(0, 0),
            body: vec![Stmt::If {
                cond: bool_expr(true),
                then_block: vec![return_statement()],
                else_block: None,
            }],
        };
        assert_flow(&[conditional_exposure_return], true, true, true);
    }

    #[test]
    fn outline_ids_and_typed_control_edges_are_sealed_as_one_structure() {
        let owner = CallOwner::Function("outlined_edges".into());
        let declaration_span = at(100);
        let branch_anchor = at(20);
        let loop_keyword = at(30);
        let loop_condition = at(31);
        let unsafe_keyword = at(40);
        let exposure_keyword = at(50);
        let body = vec![
            owned_decl("bytes", at(1)),
            Stmt::Unsafe {
                kw_span: unsafe_keyword,
                body: vec![owned_decl("unsafe_local", at(2))],
            },
            Stmt::If {
                cond: Expr {
                    kind: ExprKind::BoolLit(true),
                    span: branch_anchor,
                    ty: Some(Ty::Bool),
                },
                then_block: vec![Stmt::Return {
                    value: None,
                    span: at(21),
                }],
                else_block: Some(vec![owned_decl("else_local", at(22))]),
            },
            Stmt::While {
                cond: Expr {
                    kind: ExprKind::BoolLit(false),
                    span: loop_condition,
                    ty: Some(Ty::Bool),
                },
                invariants: Vec::new(),
                variant: None,
                kw_span: loop_keyword,
                body: vec![owned_decl("iteration", at(32))],
            },
            Stmt::Expose {
                kw_span: exposure_keyword,
                array: "bytes".into(),
                array_span: at(51),
                mutable: false,
                ptr: "ptr".into(),
                ptr_span: at(52),
                res: "mem".into(),
                res_span: at(53),
                body: Vec::new(),
            },
        ];

        let outline = ControlOutline::build(owner, declaration_span, &body);
        let root = outline.body_block();
        let StatementPlanKind::Unsafe(unsafe_block) = outline.statement(root, 1).kind() else {
            panic!("unsafe statement lost its structural child")
        };
        let StatementPlanKind::Branch(branch_id) = outline.statement(root, 2).kind() else {
            panic!("if statement lost its structural edge")
        };
        let StatementPlanKind::Loop(loop_id) = outline.statement(root, 3).kind() else {
            panic!("while statement lost its structural edge")
        };
        let StatementPlanKind::Exposure(exposure_id) = outline.statement(root, 4).kind() else {
            panic!("exposure statement lost its structural edge")
        };
        let outlined_branch = outline.branch(branch_id);
        let outlined_loop = outline.loop_plan(loop_id);
        let outlined_exposure = outline.exposure(exposure_id);

        assert_eq!(outline.block(root).parent(), None);
        assert_eq!(outline.block(root).kind(), BlockKind::Body);
        assert_eq!(outline.block(unsafe_block).parent(), Some(root));
        assert_eq!(outline.block(unsafe_block).kind(), BlockKind::Unsafe);
        assert_eq!(outline.block(unsafe_block).scope(), outline.body_scope());
        assert_eq!(
            outline.block(outlined_branch.then_block()).parent(),
            Some(root)
        );
        assert_eq!(
            outline.block(outlined_loop.body()).kind(),
            BlockKind::LoopBody
        );
        assert_eq!(
            outline.block(outlined_exposure.body()).kind(),
            BlockKind::Exposure
        );

        let plan = BodyPlan::seal(&outline, &[], &body)
            .expect("typed sealing should enrich the exact retained outline");
        assert_eq!(plan.body_block().id(), root);
        assert_eq!(plan.block(unsafe_block), outline.block(unsafe_block));

        let branch = plan
            .branch(outline.body_scope(), branch_anchor, true)
            .expect("branch has one stable parent/anchor identity");
        assert_eq!(branch.parent_scope(), outline.body_scope());
        assert_eq!(branch.anchor(), branch_anchor);
        assert_eq!(branch.then_arm().block(), outlined_branch.then_block());
        assert_eq!(
            branch.then_arm().scope(),
            outline.block(outlined_branch.then_block()).scope()
        );
        assert!(branch.then_arm().flow().definitely_returns());
        assert!(branch.then_arm().normal_exit().is_none());
        let else_arm = branch.else_arm().expect("source has an else arm");
        assert!(else_arm.flow().can_fall_through());
        assert_eq!(
            else_arm
                .normal_exit()
                .expect("else reaches continuation")
                .kind(),
            ExitKind::Fallthrough
        );
        assert!(branch.flow().can_fall_through());

        let loop_plan = plan
            .loop_plan(outline.body_scope(), loop_keyword, loop_condition)
            .expect("loop has one stable parent/header identity");
        assert_eq!(loop_plan.body(), outlined_loop.body());
        assert_eq!(
            loop_plan.body_scope(),
            outline.block(outlined_loop.body()).scope()
        );
        assert!(loop_plan.body_flow().can_fall_through());
        assert_eq!(
            loop_plan
                .backedge()
                .expect("loop body reaches its header")
                .kind(),
            ExitKind::Backedge
        );
        assert_eq!(&loop_plan.effect_key().owner, outline.owner());
        assert_eq!(loop_plan.effect_key().span, loop_keyword);

        let exposure = plan
            .exposure_plan(outline.body_scope(), exposure_keyword)
            .expect("exposure has one stable parent/header identity");
        assert_eq!(exposure.body(), outlined_exposure.body());
        assert_eq!(
            exposure.body_scope(),
            outline.block(outlined_exposure.body()).scope()
        );
        assert!(exposure.body_flow().can_fall_through());
        assert_eq!(&exposure.effect_key().owner, outline.owner());
        let normal = exposure.normal().expect("body reaches the close edge");
        assert_eq!(normal.parent_scope(), outline.body_scope());
        assert_eq!(normal.capture(), &Place::local("mem"));
        assert_eq!(normal.body_exit().kind(), ExitKind::Fallthrough);
        assert_eq!(normal.rebuild().owner(), &Place::local("bytes"));
        assert_eq!(normal.rebuild().owner_span(), at(51));
        assert_eq!(normal.rebuild().owner_ty(), &Ty::array(Ty::Bool));
        assert_eq!(normal.rebuild().mutability(), Mutability::Shared);
        assert_eq!(normal.rebuild().pointer(), &Place::local("ptr"));
        assert_eq!(normal.rebuild().resource(), &Place::local("mem"));
        assert_eq!(normal.rebuild().keyword_span(), exposure_keyword);
        assert_eq!(normal.close().kind(), ExitKind::ExposureClose);
        assert!(
            normal
                .release_loan()
                .render()
                .contains("$sable$exposure_loan$")
        );
        assert!(exposure.flow().can_fall_through());
    }

    #[test]
    fn callable_reconciliation_rejects_changed_exposure_source_identity() {
        let params = [
            Param {
                name: "left".into(),
                ty: Ty::array_ref(Ty::Int(IntTy::U8), Mutability::Shared),
                span: at(1),
                consumes: false,
            },
            Param {
                name: "right".into(),
                ty: Ty::array_ref(Ty::Int(IntTy::U8), Mutability::Shared),
                span: at(2),
                consumes: false,
            },
        ];
        let keyword = at(10);
        let body = vec![Stmt::Expose {
            kw_span: keyword,
            array: "left".into(),
            array_span: at(11),
            mutable: false,
            ptr: "pointer".into(),
            ptr_span: at(12),
            res: "memory".into(),
            res_span: at(13),
            body: Vec::new(),
        }];
        let plan = BodyPlan::build(
            CallOwner::Function("exposure_source_identity".into()),
            at(100),
            &params,
            &body,
        )
        .expect("the checked exposure has one exact retained source identity");

        let mut renamed = body.clone();
        let Stmt::Expose { array, .. } = &mut renamed[0] else {
            unreachable!()
        };
        *array = "right".into();
        let renamed = plan
            .validate_callable(&params, &renamed)
            .expect_err("a same-typed immutable owner may not reuse the retained exposure");
        assert!(renamed.message.contains("exposure owner"));

        let mut respanned = body.clone();
        let Stmt::Expose { array_span, .. } = &mut respanned[0] else {
            unreachable!()
        };
        *array_span = at(14);
        let respanned = plan
            .validate_callable(&params, &respanned)
            .expect_err("the owner use span is part of the retained exposure identity");
        assert!(respanned.message.contains("exposure owner"));

        let mut changed_mutability = body.clone();
        let Stmt::Expose { mutable, .. } = &mut changed_mutability[0] else {
            unreachable!()
        };
        *mutable = true;
        let changed_mutability = plan
            .validate_callable(&params, &changed_mutability)
            .expect_err("mutability may not be reconstructed independently by a consumer");
        assert!(changed_mutability.message.contains("mutability"));
    }

    #[test]
    fn callable_reconciliation_rejects_loop_condition_respan() {
        let keyword = at(20);
        let condition = at(21);
        let body = vec![Stmt::While {
            cond: Expr {
                kind: ExprKind::BoolLit(true),
                span: condition,
                ty: Some(Ty::Bool),
            },
            invariants: Vec::new(),
            variant: None,
            kw_span: keyword,
            body: Vec::new(),
        }];
        let plan = BodyPlan::build(
            CallOwner::Function("loop_condition_identity".into()),
            at(100),
            &[],
            &body,
        )
        .expect("the loop has one exact retained condition identity");

        let mut respanned = body;
        let Stmt::While { cond, .. } = &mut respanned[0] else {
            unreachable!()
        };
        cond.span = at(22);
        let error = plan
            .validate_body_shape(&respanned)
            .expect_err("a changed condition span may not reuse the retained loop edge");
        assert!(error.message.contains("condition"));
    }

    #[test]
    fn body_plan_orders_nested_return_backedge_and_frame_cleanup() {
        let condition = Expr {
            kind: ExprKind::BoolLit(true),
            span: at(20),
            ty: Some(Ty::Bool),
        };
        let body = vec![
            owned_decl("root", at(1)),
            Stmt::Unsafe {
                kw_span: at(2),
                body: vec![owned_decl("unsafe_local", at(3))],
            },
            Stmt::If {
                cond: condition,
                then_block: vec![
                    owned_decl("branch", at(4)),
                    Stmt::While {
                        cond: bool_expr(true),
                        invariants: Vec::new(),
                        variant: None,
                        kw_span: at(30),
                        body: vec![
                            owned_decl("iteration", at(5)),
                            Stmt::Return {
                                value: Some(bool_expr(true)),
                                span: at(40),
                            },
                        ],
                    },
                ],
                else_block: Some(vec![owned_decl("other", at(6))]),
            },
        ];
        let params = vec![Param {
            name: "argument".into(),
            ty: Ty::array(Ty::Bool),
            span: at(7),
            consumes: false,
        }];
        let plan = BodyPlan::build(
            CallOwner::Function("control_test_routes".into()),
            at(100),
            &params,
            &body,
        )
        .expect("distinct structural anchors form a plan");

        let loop_scope = plan
            .scope_for(ScopeKind::LoopBody, at(30))
            .expect("loop scope");
        let backedge = plan.scope_exit(loop_scope);
        assert_eq!(backedge.kind(), ExitKind::Backedge);
        assert_eq!(backedge.scopes(), &[loop_scope]);
        assert_eq!(drop_names(&plan, &backedge), ["iteration"]);
        assert_eq!(clear_names(&backedge), ["iteration"]);

        let returned = plan
            .explicit_return(at(40), loop_scope)
            .expect("return route");
        assert_eq!(returned.lexical().kind(), ExitKind::Return);
        assert_eq!(
            drop_names(&plan, returned.lexical()),
            ["iteration", "branch", "unsafe_local", "root"]
        );
        assert_eq!(
            clear_names(returned.lexical()),
            ["iteration", "branch", "unsafe_local", "root"]
        );
        assert_eq!(drop_names(&plan, returned.frame()), ["argument"]);
        assert_eq!(clear_names(returned.frame()), ["argument"]);
        let result_slot = returned.result_slot().expect("explicit result slot");
        assert!(result_slot.render().starts_with("$sable$return$40$41$"));
        assert!(
            !returned
                .lexical()
                .clears()
                .iter()
                .any(|place| place == result_slot)
        );
        assert!(plan.implicit_return().result_slot().is_none());

        let unsafe_drop = plan
            .candidate_for_place(&Place::local("unsafe_local"))
            .expect("unsafe local is cleanup-bearing");
        assert_eq!(unsafe_drop.scope(), plan.body_scope());

        let trap = plan.trap_route();
        assert_eq!(trap.kind(), ExitKind::Trap);
        assert!(trap.scopes().is_empty());
        assert!(trap.clears().is_empty());
        assert!(trap.drops().is_empty());
    }

    #[test]
    fn duplicate_structural_scope_keys_fail_closed() {
        let duplicate_anchor = at(10);
        let body = vec![
            Stmt::While {
                cond: bool_expr(true),
                invariants: Vec::new(),
                variant: None,
                kw_span: duplicate_anchor,
                body: Vec::new(),
            },
            Stmt::While {
                cond: bool_expr(false),
                invariants: Vec::new(),
                variant: None,
                kw_span: duplicate_anchor,
                body: Vec::new(),
            },
        ];
        let error = BodyPlan::build(
            CallOwner::Function("control_test_duplicate".into()),
            at(100),
            &[],
            &body,
        )
        .expect_err("duplicate stable keys must not fall back to traversal order");
        assert_eq!(error.span, duplicate_anchor);
        assert!(error.message.contains("duplicate LoopBody scope anchor"));
    }

    #[test]
    fn compiler_temporaries_have_stable_lifetimes_in_the_control_plan() {
        let literal_span = at(10);
        let exposure_span = at(20);
        let body = vec![
            Stmt::Decl {
                ty: Ty::array(Ty::Bool),
                name: "values".into(),
                name_span: at(9),
                init: Some(Expr {
                    kind: ExprKind::ArrayLit(vec![bool_expr(true), bool_expr(false)]),
                    span: literal_span,
                    ty: Some(Ty::array(Ty::Bool)),
                }),
                mutable: true,
            },
            Stmt::Expose {
                kw_span: exposure_span,
                array: "values".into(),
                array_span: at(21),
                mutable: true,
                ptr: "ptr".into(),
                ptr_span: at(22),
                res: "mem".into(),
                res_span: at(23),
                body: Vec::new(),
            },
        ];
        let build = || {
            BodyPlan::build(
                CallOwner::Function("control_test_temporaries".into()),
                at(100),
                &[],
                &body,
            )
            .expect("temporary sites are structurally unique")
        };
        let plan = build();
        let body_exit = plan.scope_exit(plan.body_scope());
        let body_names = clear_names(&body_exit);
        assert!(body_names[0].contains("$sable$bool_element$"));
        assert!(body_names[1].contains("$sable$bool_element$"));
        assert_eq!(body_names[2], "values");

        let exposure = plan
            .scope_for(ScopeKind::Exposure, exposure_span)
            .expect("exposure scope");
        assert_eq!(clear_names(&plan.scope_exit(exposure)), ["mem", "ptr"]);
        let close = plan
            .exposure_close(exposure, exposure_span)
            .expect("exposure close route");
        assert_eq!(close.kind(), ExitKind::ExposureClose);
        let close_names = clear_names(&close);
        assert!(close_names[0].contains("$sable$exposure_byte$"));
        assert!(close_names[1].contains("$sable$exposure_index$"));
        assert!(close_names[2].contains("$sable$exposure_loan$"));

        let rebuilt = build();
        assert_eq!(
            clear_names(&rebuilt.scope_exit(rebuilt.body_scope())),
            body_names
        );
    }

    #[test]
    fn assignment_actions_seal_scope_destination_drop_and_staging() {
        let branch_anchor = at(20);
        let loop_anchor = at(30);
        let assignment_span = at(40);
        let assign = |name: &str| Stmt::Assign {
            name: name.into(),
            name_span: assignment_span,
            value: if name == "owner" {
                fresh_class_expr(at(41))
            } else {
                bool_expr(true)
            },
        };
        let body = vec![
            Stmt::Decl {
                ty: Ty::Class(0),
                name: "owner".into(),
                name_span: at(1),
                init: None,
                mutable: true,
            },
            Stmt::Decl {
                ty: Ty::Bool,
                name: "flag".into(),
                name_span: at(2),
                init: Some(bool_expr(false)),
                mutable: true,
            },
            Stmt::If {
                cond: Expr {
                    kind: ExprKind::BoolLit(true),
                    span: branch_anchor,
                    ty: Some(Ty::Bool),
                },
                then_block: vec![assign("owner")],
                else_block: Some(vec![assign("flag")]),
            },
            Stmt::While {
                cond: bool_expr(false),
                invariants: Vec::new(),
                variant: None,
                kw_span: loop_anchor,
                body: vec![assign("owner")],
            },
        ];
        let build = || {
            BodyPlan::build(
                CallOwner::Function("assignment_actions".into()),
                at(100),
                &[],
                &body,
            )
            .expect("assignment sites have stable structural identities")
        };
        let plan = build();
        assert_eq!(plan.assignments().len(), 3);
        let then_scope = plan
            .scope_for(ScopeKind::BranchArm(BranchArm::Then), branch_anchor)
            .unwrap();
        let else_scope = plan
            .scope_for(ScopeKind::BranchArm(BranchArm::Else), branch_anchor)
            .unwrap();
        let loop_scope = plan.scope_for(ScopeKind::LoopBody, loop_anchor).unwrap();

        let then_action = plan
            .assignment(then_scope, assignment_span, &Place::local("owner"))
            .unwrap();
        assert_eq!(then_action.scope(), then_scope);
        assert_eq!(then_action.ty(), &Ty::Class(0));
        assert_eq!(
            then_action.transfer_key(),
            &ValueTransferKey {
                owner: CallOwner::Function("assignment_actions".into()),
                span: at(41),
                sink: ValueTransferSink::Assignment(Place::local("owner")),
            }
        );
        assert!(then_action.previous().is_some());
        let AssignmentStaging::Temporary(then_temp) = then_action.staging() else {
            panic!("class replacement must stage its RHS")
        };
        assert!(then_temp.render().contains("$sable$assignment$"));

        let else_action = plan
            .assignment(else_scope, assignment_span, &Place::local("flag"))
            .unwrap();
        assert_eq!(else_action.scope(), else_scope);
        assert_eq!(else_action.ty(), &Ty::Bool);
        assert_eq!(else_action.previous(), None);
        assert_eq!(else_action.staging(), &AssignmentStaging::Direct);

        let loop_action = plan
            .assignment(loop_scope, assignment_span, &Place::local("owner"))
            .unwrap();
        assert_eq!(loop_action.previous(), then_action.previous());
        let AssignmentStaging::Temporary(loop_temp) = loop_action.staging() else {
            panic!("loop replacement must stage its RHS")
        };
        assert_ne!(then_temp, loop_temp);

        let rebuilt = build();
        let rebuilt_then = rebuilt
            .scope_for(ScopeKind::BranchArm(BranchArm::Then), branch_anchor)
            .unwrap();
        assert_eq!(
            rebuilt
                .assignment(rebuilt_then, assignment_span, &Place::local("owner"))
                .unwrap()
                .staging(),
            then_action.staging()
        );
    }

    #[test]
    fn assignment_action_keys_and_destinations_fail_closed() {
        let same_span = at(10);
        let declaration = Stmt::Decl {
            ty: Ty::Bool,
            name: "left".into(),
            name_span: at(1),
            init: Some(bool_expr(false)),
            mutable: true,
        };
        let assignment = |name: &str| Stmt::Assign {
            name: name.into(),
            name_span: same_span,
            value: bool_expr(true),
        };
        let duplicate = BodyPlan::build(
            CallOwner::Function("duplicate_assignments".into()),
            at(100),
            &[],
            &[declaration.clone(), assignment("left"), assignment("left")],
        )
        .expect_err("one scope/span pair cannot identify two assignments");
        assert_eq!(duplicate.span, same_span);
        assert!(duplicate.message.contains("duplicate assignment span"));

        let before_declaration = BodyPlan::build(
            CallOwner::Function("assignment_before_binding".into()),
            at(100),
            &[],
            &[assignment("left"), declaration.clone()],
        )
        .expect_err("an assignment cannot borrow a later binding identity");
        assert!(
            before_declaration
                .message
                .contains("no preceding planned binding")
        );

        let sibling = BodyPlan::build(
            CallOwner::Function("sibling_assignment".into()),
            at(100),
            &[],
            &[Stmt::If {
                cond: Expr {
                    kind: ExprKind::BoolLit(true),
                    span: at(20),
                    ty: Some(Ty::Bool),
                },
                then_block: vec![declaration.clone()],
                else_block: Some(vec![assignment("left")]),
            }],
        )
        .expect_err("a sibling branch cannot reuse another arm's binding");
        assert!(sibling.message.contains("outside this scope"));

        let plan = BodyPlan::build(
            CallOwner::Function("tampered_assignment".into()),
            at(100),
            &[],
            &[declaration, assignment("left")],
        )
        .unwrap();
        let error = plan
            .assignment(plan.body_scope(), same_span, &Place::local("right"))
            .expect_err("a changed destination must not reuse the original action");
        assert!(error.message.contains("targets `left`, not `right`"));
    }

    #[test]
    fn trap_sites_have_injective_structural_identity_and_empty_routes() {
        let trap_span = at(10);
        let expression = arithmetic_expr(BinOp::Add, trap_span);
        let duplicate = BodyPlan::build(
            CallOwner::Function("duplicate_traps".into()),
            at(100),
            &[],
            &[
                Stmt::ExprStmt(expression.clone()),
                Stmt::ExprStmt(expression.clone()),
            ],
        )
        .expect_err("cloned trap sites may not receive traversal identities");
        assert_eq!(duplicate.span, trap_span);
        assert!(duplicate.message.contains("duplicate AddOverflow"));

        let branch_anchor = at(20);
        let body = [Stmt::If {
            cond: Expr {
                kind: ExprKind::BoolLit(true),
                span: branch_anchor,
                ty: Some(Ty::Bool),
            },
            then_block: vec![Stmt::ExprStmt(expression.clone())],
            else_block: Some(vec![Stmt::ExprStmt(expression.clone())]),
        }];
        let plan = BodyPlan::build(
            CallOwner::Function("scoped_traps".into()),
            at(101),
            &[],
            &body,
        )
        .expect("the active lexical scope distinguishes sibling sites");
        for arm in [BranchArm::Then, BranchArm::Else] {
            let scope = plan
                .scope_for(ScopeKind::BranchArm(arm), branch_anchor)
                .unwrap();
            let sites = plan.expression_trap_sites(scope, &expression).unwrap();
            assert_eq!(sites.len(), 1);
            assert_eq!(sites[0].scope(), scope);
            assert_eq!(sites[0].span(), trap_span);
            assert_eq!(sites[0].route().kind(), ExitKind::Trap);
            assert!(sites[0].route().scopes().is_empty());
            assert!(sites[0].route().clears().is_empty());
            assert!(sites[0].route().drops().is_empty());
        }
    }

    #[test]
    fn body_reconciliation_rejects_missing_mismatched_and_moved_trap_sites() {
        let trap_span = at(10);
        let original = arithmetic_expr(BinOp::Add, trap_span);
        let direct_body = vec![Stmt::ExprStmt(original.clone())];
        let direct = BodyPlan::build(
            CallOwner::Function("changed_trap".into()),
            at(100),
            &[],
            &direct_body,
        )
        .unwrap();
        let missing = direct
            .validate_body_shape(&[])
            .expect_err("deleting a sealed trap site must fail");
        assert!(missing.message.contains("planned trap site"));

        let mismatched = [Stmt::ExprStmt(arithmetic_expr(BinOp::Sub, trap_span))];
        let mismatch = direct
            .validate_body_shape(&mismatched)
            .expect_err("a different operation may not reuse the old site");
        assert!(mismatch.message.contains("SubOverflow"));

        let branch_anchor = at(30);
        let branch_body = vec![Stmt::If {
            cond: Expr {
                kind: ExprKind::BoolLit(true),
                span: branch_anchor,
                ty: Some(Ty::Bool),
            },
            then_block: vec![Stmt::ExprStmt(original.clone())],
            else_block: Some(Vec::new()),
        }];
        let branch = BodyPlan::build(
            CallOwner::Function("moved_trap".into()),
            at(101),
            &[],
            &branch_body,
        )
        .unwrap();
        let moved = [Stmt::If {
            cond: Expr {
                kind: ExprKind::BoolLit(true),
                span: branch_anchor,
                ty: Some(Ty::Bool),
            },
            then_block: Vec::new(),
            else_block: Some(vec![Stmt::ExprStmt(original)]),
        }];
        let moved = branch
            .validate_body_shape(&moved)
            .expect_err("moving a site to a sibling scope changes its identity");
        assert!(moved.message.contains("active lexical scope"));
    }

    #[test]
    fn callable_reconciliation_covers_scope_reuse_bindings_candidates_and_parameters() {
        let branch_anchor = at(20);
        let branch = Stmt::If {
            cond: Expr {
                kind: ExprKind::BoolLit(true),
                span: branch_anchor,
                ty: Some(Ty::Bool),
            },
            then_block: Vec::new(),
            else_block: None,
        };
        let branch_plan = BodyPlan::build(
            CallOwner::Function("reused_scope".into()),
            at(100),
            &[],
            std::slice::from_ref(&branch),
        )
        .unwrap();
        let duplicate_scope = branch_plan
            .validate_body_shape(&[branch.clone(), branch])
            .expect_err("cloned empty scopes need an injective identity too");
        assert!(
            duplicate_scope
                .message
                .contains("reuse one checked structural identity")
        );

        let declaration = owned_decl("owner", at(40));
        let declaration_plan = BodyPlan::build(
            CallOwner::Function("binding_shape".into()),
            at(101),
            &[],
            std::slice::from_ref(&declaration),
        )
        .unwrap();
        let mut renamed = declaration.clone();
        let Stmt::Decl { name, .. } = &mut renamed else {
            unreachable!()
        };
        *name = "renamed".into();
        assert!(
            declaration_plan.validate_body_shape(&[renamed]).is_err(),
            "an otherwise-unused source binding cannot be renamed under a stale plan"
        );
        assert!(
            declaration_plan.validate_body_shape(&[]).is_err(),
            "deleting a cleanup-bearing declaration cannot leave an unvisited DropId"
        );

        let params = [Param {
            name: "input".into(),
            ty: Ty::array(Ty::Bool),
            span: at(50),
            consumes: false,
        }];
        let parameter_plan = BodyPlan::build(
            CallOwner::Function("parameter_shape".into()),
            at(102),
            &params,
            &[],
        )
        .unwrap();
        let mut changed_name = params.clone();
        changed_name[0].name = "other".into();
        assert!(
            parameter_plan
                .validate_callable(&changed_name, &[])
                .is_err()
        );
        let mut changed_type = params.clone();
        changed_type[0].ty = Ty::Bool;
        assert!(
            parameter_plan
                .validate_callable(&changed_type, &[])
                .is_err()
        );
    }

    #[test]
    fn control_program_indexes_every_executable_or_verified_body_by_typed_owner() {
        let mut source = program();
        source.fns.push(function("free", at(100), "free_owner"));
        source
            .fns
            .push(function("test_dynamic", at(200), "test_owner"));
        let mut template = function("template", at(300), "template_owner");
        template.type_params.push("T".into());
        template.type_bounds.push(None);
        source.fn_templates.push(template);
        source.classes.push(class("Concrete", at(400), "concrete"));
        let mut template_class = class("Generic", at(500), "generic");
        template_class.type_params.push("T".into());
        template_class.type_bounds.push(None);
        source.class_templates.push(template_class);

        let control = ControlProgram::build(&source).expect("typed bodies form one table");
        assert!(!control.is_empty());
        assert_eq!(control.len(), 9);

        let expected = [
            CallOwner::Function("free".into()),
            CallOwner::Function("test_dynamic".into()),
            CallOwner::Function("template".into()),
            CallOwner::Constructor {
                class: "Concrete".into(),
                init: "same".into(),
            },
            CallOwner::Method {
                class: "Concrete".into(),
                method: "same".into(),
            },
            CallOwner::Deinitializer {
                class: "Concrete".into(),
            },
            CallOwner::Constructor {
                class: "Generic".into(),
                init: "same".into(),
            },
            CallOwner::Method {
                class: "Generic".into(),
                method: "same".into(),
            },
            CallOwner::Deinitializer {
                class: "Generic".into(),
            },
        ];
        assert_eq!(
            control.iter().map(ControlBody::owner).collect::<Vec<_>>(),
            expected.iter().collect::<Vec<_>>()
        );

        let constructor = control
            .body(&expected[3], at(900))
            .expect("constructor has an exact typed lookup");
        let method = control
            .body(&expected[4], at(901))
            .expect("same-spelled method remains distinct");
        assert_eq!(constructor.owner(), constructor.plan().owner());
        assert_eq!(method.owner(), method.plan().owner());
        assert_eq!(constructor.declaration_span(), at(410));
        assert_eq!(method.declaration_span(), at(420));
        assert!(
            constructor
                .plan()
                .candidate_for_place(&Place::local("concrete_init_owner"))
                .is_some()
        );
        assert!(
            constructor
                .plan()
                .candidate_for_place(&Place::local("concrete_method_owner"))
                .is_none()
        );
        assert!(
            method
                .plan()
                .candidate_for_place(&Place::local("concrete_method_owner"))
                .is_some()
        );

        let missing_span = at(999);
        let error = control
            .body(&CallOwner::Function("absent".into()), missing_span)
            .expect_err("missing bodies may not fall back to rebuilding a plan");
        assert_eq!(error.span, missing_span);
        assert!(error.message.contains("function `absent`"));
    }

    #[test]
    fn value_drop_actions_seal_only_current_recursive_cleanup_shapes() {
        let span = at(390);

        let class_ty = Ty::Class(2);
        let class = ValueDropAction::build(&class_ty, span)
            .unwrap()
            .expect("class owns one concrete destruction recipe");
        assert_eq!(class.ty(), &class_ty);
        let ValueDropRecipe::DropClass(class_drop) = class.recipe() else {
            panic!("class action must terminate in a class recipe")
        };
        assert_eq!(class_drop.class(), 2);
        assert!(class_drop.terminal_trap_route().is_terminal_trap());

        let array_ty = Ty::array(Ty::Bool);
        let array = ValueDropAction::build(&array_ty, span)
            .unwrap()
            .expect("current arrays release one non-affine buffer");
        assert!(matches!(
            array.recipe(),
            ValueDropRecipe::ReleaseArray { element: Ty::Bool }
        ));

        let option_array_ty = Ty::option(array_ty.clone());
        let option_array = ValueDropAction::build(&option_array_ty, span)
            .unwrap()
            .expect("an admitted owning option seals its present payload");
        let ValueDropRecipe::DropPresent(payload) = option_array.recipe() else {
            panic!("owning option must retain a present-only recipe")
        };
        assert_eq!(payload.ty(), &array_ty);
        assert!(matches!(
            payload.recipe(),
            ValueDropRecipe::ReleaseArray { element: Ty::Bool }
        ));

        let option_class_ty = Ty::option(Ty::Class(2));
        let option_class = ValueDropAction::build(&option_class_ty, span)
            .unwrap()
            .expect("an admitted class option seals its present class recipe");
        let ValueDropRecipe::DropPresent(payload) = option_class.recipe() else {
            panic!("owning option must retain a present-only recipe")
        };
        assert!(matches!(
            payload.recipe(),
            ValueDropRecipe::DropClass(action) if action.class() == 2
        ));

        for non_cleanup in [
            Ty::Bool,
            Ty::option(Ty::Bool),
            Ty::Res(crate::ast::ResKind::RawSpan),
        ] {
            assert!(
                ValueDropAction::build(&non_cleanup, span)
                    .unwrap()
                    .is_none()
            );
        }

        for unsupported in [
            Ty::array(Ty::Class(2)),
            Ty::option(Ty::option(Ty::Class(2))),
            Ty::option(Ty::array(Ty::Int(IntTy::U64))),
            Ty::option(Ty::Res(crate::ast::ResKind::RawSpan)),
        ] {
            let error = ValueDropAction::build(&unsupported, span)
                .expect_err("unsealed owner nesting must fail before it acquires cleanup");
            assert_eq!(error.span, span);
            assert!(
                error.message.contains("occupied-slot")
                    || error.message.contains("one-level cleanup family"),
                "unexpected refusal for `{}`: {}",
                unsupported.name(),
                error.message
            );
        }
    }

    #[test]
    fn class_drop_fields_carry_recursive_actions_but_resources_remain_must_consume() {
        let mut owner = class("Owner", at(395), "owner");
        owner.fields = vec![
            Field {
                name: "child".into(),
                ty: Ty::Class(0),
                span: at(396),
                must_consume: false,
            },
            Field {
                name: "bytes".into(),
                ty: Ty::array(Ty::Bool),
                span: at(397),
                must_consume: false,
            },
            Field {
                name: "authority".into(),
                ty: Ty::Res(crate::ast::ResKind::RawSpan),
                span: at(398),
                must_consume: true,
            },
        ];
        let plan = ClassDropPlan::build(1, &owner).expect("current field shapes seal");
        let fields = plan
            .phases()
            .iter()
            .filter_map(|phase| match phase {
                ClassDropPhase::DropField(field) => Some(field),
                ClassDropPhase::CheckInvariant | ClassDropPhase::RunDeinitializer(_) => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            fields.iter().map(|field| field.name()).collect::<Vec<_>>(),
            ["authority", "bytes", "child"]
        );
        assert!(fields[0].must_consume());
        assert!(fields[0].drop_action().is_none());
        assert!(matches!(
            fields[1].drop_action().map(ValueDropAction::recipe),
            Some(ValueDropRecipe::ReleaseArray { element: Ty::Bool })
        ));
        assert!(matches!(
            fields[2].drop_action().map(ValueDropAction::recipe),
            Some(ValueDropRecipe::DropClass(action)) if action.class() == 0
        ));

        owner.fields[1].ty = Ty::array(Ty::Class(0));
        let error = ClassDropPlan::build(1, &owner)
            .expect_err("owner arrays need occupied-slot semantics before field cleanup");
        assert_eq!(error.span, at(397));
        assert!(error.message.contains("occupied-slot"));
    }

    #[test]
    fn concrete_class_drop_plan_seals_exact_identity_order_and_no_unwind() {
        let mut source = program();
        let mut concrete = class("Owner", at(400), "owner");
        concrete.fields = vec![
            Field {
                name: "first".into(),
                ty: Ty::Int(IntTy::U64),
                span: at(401),
                must_consume: false,
            },
            Field {
                name: "second".into(),
                ty: Ty::Bool,
                span: at(402),
                must_consume: false,
            },
            Field {
                name: "third".into(),
                ty: Ty::array(Ty::Bool),
                span: at(403),
                must_consume: false,
            },
        ];
        concrete.invariants = vec![Clause {
            kind: ClauseKind::Invariant,
            label: Some("owner_live".into()),
            fact: false,
            unfold: false,
            text: "true".into(),
            span: at(404),
            line_span: at(405),
        }];
        concrete.deinit = Some(Vec::new());
        source.classes.push(concrete.clone());

        let control = ControlProgram::build(&source).expect("concrete class has one drop plan");
        let plan = control
            .class_drop(0, &source.classes[0])
            .expect("exact concrete declaration resolves its drop plan");
        assert_eq!(plan.class(), 0);
        assert_eq!(plan.class_name(), "Owner");
        assert_eq!(control.class_drops().len(), 1);
        assert_eq!(plan.terminal_trap_route().kind(), ExitKind::Trap);
        assert!(plan.terminal_trap_route().scopes().is_empty());
        assert!(plan.terminal_trap_route().clears().is_empty());
        assert!(plan.terminal_trap_route().drops().is_empty());

        assert!(matches!(plan.phases()[0], ClassDropPhase::CheckInvariant));
        assert!(matches!(
            &plan.phases()[1],
            ClassDropPhase::RunDeinitializer(CallOwner::Deinitializer { class })
                if class == "Owner"
        ));
        let fields = plan.phases()[2..]
            .iter()
            .map(|phase| match phase {
                ClassDropPhase::DropField(field) => {
                    (field.index(), field.name(), field.ty().clone())
                }
                _ => panic!("only field phases follow the deinitializer"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            fields,
            vec![
                (2, "third", Ty::array(Ty::Bool)),
                (1, "second", Ty::Bool),
                (0, "first", Ty::Int(IntTy::U64)),
            ]
        );
        let ClassDropPhase::DropField(array_field) = &plan.phases()[2] else {
            unreachable!()
        };
        assert!(matches!(
            array_field.drop_action().map(ValueDropAction::recipe),
            Some(ValueDropRecipe::ReleaseArray { element: Ty::Bool })
        ));
        for phase in &plan.phases()[3..] {
            let ClassDropPhase::DropField(field) = phase else {
                unreachable!()
            };
            assert!(field.drop_action().is_none());
        }

        let mut changed_field_action = plan.clone();
        let ClassDropPhase::DropField(field) = &mut changed_field_action.phases[2] else {
            unreachable!()
        };
        let Some(action) = &mut field.drop_action else {
            unreachable!()
        };
        let ValueDropRecipe::ReleaseArray { element } = &mut action.recipe else {
            unreachable!()
        };
        *element = Ty::Int(IntTy::U8);
        assert!(changed_field_action.validate(0, &concrete).is_err());

        let mut reordered = concrete.clone();
        reordered.fields.swap(0, 1);
        let mut changed_contract = concrete.clone();
        changed_contract.invariants[0].text = "false".into();
        let mut moved_field = concrete.clone();
        moved_field.fields[0].span = at(999);
        let mut removed_deinitializer = concrete;
        removed_deinitializer.deinit = None;
        for changed in [
            reordered,
            changed_contract,
            moved_field,
            removed_deinitializer,
        ] {
            let error = control
                .class_drop(0, &changed)
                .expect_err("post-check class-drop shape mutation must fail closed");
            assert!(error.message.contains("no longer matches its declaration"));
        }
    }

    #[test]
    fn field_replacement_and_discarded_class_actions_seal_exact_order_and_links() {
        let owner = CallOwner::Function("cleanup_actions".into());
        let body = cleanup_action_body();
        let plan = BodyPlan::build(owner.clone(), at(1), &[], &body)
            .expect("checked cleanup sites have retained actions");

        let class_assignment = plan
            .field_assignment(
                plan.body_scope(),
                at(10),
                &Place::field("self", "child"),
                match &body[0] {
                    Stmt::FieldAssign { value, .. } => value,
                    _ => unreachable!(),
                },
            )
            .expect("class field action exact-lookups by destination and RHS");
        assert_eq!(class_assignment.scope(), plan.body_scope());
        assert_eq!(class_assignment.ty(), &Ty::Class(0));
        assert!(class_assignment.drop_if_present());
        assert_eq!(
            class_assignment.transfer_key(),
            &ValueTransferKey {
                owner: owner.clone(),
                span: at(11),
                sink: ValueTransferSink::FieldAssignment(Place::field("self", "child")),
            }
        );
        assert!(matches!(
            class_assignment.staging(),
            AssignmentStaging::Temporary(place)
                if place == plan
                    .compiler_temp(
                        plan.body_scope(),
                        at(10),
                        CompilerTempKind::FieldAssignmentValue,
                    )
                    .unwrap()
        ));
        let Some(class_action) = class_assignment.drop_action() else {
            unreachable!()
        };
        let ValueDropRecipe::DropClass(class_drop) = class_action.recipe() else {
            unreachable!()
        };
        assert_eq!(class_drop.class(), 0);
        assert!(class_drop.terminal_trap_route().is_terminal_trap());

        let scalar_assignment = plan
            .field_assignment(
                plan.body_scope(),
                at(20),
                &Place::field("self", "count"),
                match &body[1] {
                    Stmt::FieldAssign { value, .. } => value,
                    _ => unreachable!(),
                },
            )
            .expect("non-cleanup field installs use the same typed action");
        assert!(!scalar_assignment.drop_if_present());
        assert_eq!(scalar_assignment.staging(), &AssignmentStaging::Direct);
        assert!(scalar_assignment.drop_action().is_none());

        let discarded = plan
            .temporary_drop(
                plan.body_scope(),
                match &body[2] {
                    Stmt::ExprStmt(expression) => expression,
                    _ => unreachable!(),
                },
            )
            .expect("fresh class result has one statement-end drop action");
        assert_eq!(discarded.scope(), plan.body_scope());
        assert_eq!(discarded.ty(), &Ty::Class(0));
        assert!(matches!(
            discarded.drop_action().recipe(),
            ValueDropRecipe::DropClass(class) if class.class() == 0
        ));
        assert_eq!(
            discarded.transfer_key(),
            &ValueTransferKey {
                owner,
                span: at(30),
                sink: ValueTransferSink::DiscardTemporary,
            }
        );
        assert_eq!(
            discarded.temporary(),
            plan.compiler_temp(
                plan.body_scope(),
                at(30),
                CompilerTempKind::DiscardedClassValue,
            )
            .unwrap()
        );
    }

    #[test]
    fn cleanup_action_reconciliation_rejects_deletion_destination_type_and_span_tamper() {
        let body = cleanup_action_body();
        let plan = BodyPlan::build(
            CallOwner::Function("cleanup_tamper".into()),
            at(1),
            &[],
            &body,
        )
        .expect("baseline plan");

        let mut deleted_field = plan.clone();
        deleted_field.field_assignments.clear();
        assert!(deleted_field.validate_body_shape(&body).is_err());
        let mut deleted_temporary = plan.clone();
        deleted_temporary.temporary_drop_ids.clear();
        assert!(deleted_temporary.validate_body_shape(&body).is_err());

        let mut changed_destination = body.clone();
        let Stmt::FieldAssign { field, .. } = &mut changed_destination[0] else {
            unreachable!()
        };
        *field = "other".into();
        assert!(plan.validate_body_shape(&changed_destination).is_err());

        let mut changed_type = body.clone();
        let Stmt::FieldAssign { value, .. } = &mut changed_type[0] else {
            unreachable!()
        };
        value.ty = Some(Ty::Class(1));
        assert!(plan.validate_body_shape(&changed_type).is_err());

        let mut changed_field_span = body.clone();
        let Stmt::FieldAssign { field_span, .. } = &mut changed_field_span[0] else {
            unreachable!()
        };
        *field_span = at(99);
        assert!(plan.validate_body_shape(&changed_field_span).is_err());

        let mut changed_value_span = body.clone();
        let Stmt::FieldAssign { value, .. } = &mut changed_value_span[0] else {
            unreachable!()
        };
        value.span = at(98);
        assert!(plan.validate_body_shape(&changed_value_span).is_err());

        let mut changed_discard_span = body.clone();
        let Stmt::ExprStmt(expression) = &mut changed_discard_span[2] else {
            unreachable!()
        };
        expression.span = at(97);
        assert!(plan.validate_body_shape(&changed_discard_span).is_err());

        let mut forged_destination = plan.clone();
        forged_destination.field_assignments[0].destination = Place::field("self", "other");
        assert!(forged_destination.validate_body_shape(&body).is_err());
        let mut forged_class = plan.clone();
        let ValueDropRecipe::DropClass(class) =
            &mut forged_class.temporary_drops[0].drop_action.recipe
        else {
            unreachable!("discarded class result retains a class recipe")
        };
        class.class = 1;
        assert!(forged_class.validate_body_shape(&body).is_err());
    }

    #[test]
    fn cleanup_action_class_links_resolve_only_the_exact_concrete_drop_recipe() {
        let mut source = program();
        let mut child = class("Child", at(100), "child");
        child.inits.clear();
        child.methods.clear();
        child.deinit = None;
        source.classes.push(child);
        let mut subject = function("cleanup_links", at(200), "unused");
        subject.body = cleanup_action_body();
        source.fns.push(subject);

        let control = ControlProgram::build(&source).expect("all cleanup links resolve at seal");
        let body = control
            .body(&CallOwner::Function("cleanup_links".into()), at(200))
            .unwrap();
        let action = body.plan().temporary_drops().next().unwrap();
        let ValueDropRecipe::DropClass(class_action) = action.drop_action().recipe() else {
            unreachable!()
        };
        let drop = control
            .class_drop_for_action(class_action, &source.classes, action.span())
            .expect("action links the exact concrete class recipe");
        assert_eq!(drop.class(), 0);

        let mut wrong_class = class_action.clone();
        wrong_class.class = 1;
        assert!(
            control
                .class_drop_for_action(&wrong_class, &source.classes, action.span())
                .is_err()
        );
        let mut unwind = class_action.clone();
        unwind.terminal_trap = ExitRoute {
            kind: ExitKind::Return,
            scopes: vec![body.plan().body_scope()],
            clears: Vec::new(),
            drops: Vec::new(),
        };
        assert!(
            control
                .class_drop_for_action(&unwind, &source.classes, action.span())
                .is_err()
        );

        let option_ty = Ty::option(Ty::Class(0));
        let option_action = ValueDropAction::build(&option_ty, action.span())
            .unwrap()
            .expect("class option has one recursive action");
        control
            .validate_value_drop_action(&option_action, &source.classes, action.span())
            .expect("the exact nested class leaf resolves through the same table");

        let mut wrong_payload_ty = option_action.clone();
        let ValueDropRecipe::DropPresent(payload) = &mut wrong_payload_ty.recipe else {
            unreachable!()
        };
        payload.ty = Ty::Class(1);
        assert!(
            control
                .validate_value_drop_action(&wrong_payload_ty, &source.classes, action.span())
                .is_err()
        );

        let mut wrong_array_element =
            ValueDropAction::build(&Ty::option(Ty::array(Ty::Bool)), action.span())
                .unwrap()
                .unwrap();
        let ValueDropRecipe::DropPresent(payload) = &mut wrong_array_element.recipe else {
            unreachable!()
        };
        let ValueDropRecipe::ReleaseArray { element } = &mut payload.recipe else {
            unreachable!()
        };
        *element = Ty::Int(IntTy::U8);
        assert!(
            control
                .validate_value_drop_action(&wrong_array_element, &source.classes, action.span())
                .is_err()
        );
    }

    #[test]
    fn control_program_rejects_duplicate_semantic_owners_before_planning_them() {
        let mut source = program();
        source.fns.push(function("same", at(100), "concrete_owner"));
        // A forged retained template with the same semantic function identity
        // must not replace the executable entry or receive a parallel plan.
        // Its duplicate local would itself be malformed if planning ran first,
        // which pins duplicate-owner refusal precedence too.
        let mut duplicate = function("same", at(200), "duplicate");
        duplicate.body.push(owned_decl("duplicate", at(202)));
        source.fn_templates.push(duplicate);

        let error = ControlProgram::build(&source)
            .expect_err("one semantic callable identity has exactly one body plan");
        assert_eq!(error.span, at(200));
        assert!(
            error
                .message
                .contains("duplicate control body identity for function `same`")
        );
    }
}
