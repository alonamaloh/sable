//! Kernel-checked certificates for selected symbolic-state transitions.
//!
//! The checker produces the stage-neutral call records; the verification
//! generator enriches them from its live environment and emits fixed-proof
//! Lean theorems. They deliberately cover only named high-risk transitions;
//! they are not a second VC language or a claim that the whole source-to-VC
//! translation is validated.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::ast::{Mutability, Ty};
use crate::control::{SlotAction, SlotActionKind};
use crate::ownership::{CheckedSlotTransition, CheckedSlotTransitionKind, ValueTransfer};
use crate::place::Place;
use crate::span::Span;
use std::collections::HashMap;

/// The resolved flavor and target of a checked source call.
///
/// The target is part of the identity rather than merely payload: if a later
/// rewrite changed what an expression called without re-running the checker,
/// VC generation must refuse the stale handoff instead of applying it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum CallTarget {
    Function(String),
    Constructor { class: String, init: String },
    Method { class: String, method: String },
}

impl CallTarget {
    pub(crate) fn render(&self) -> String {
        match self {
            Self::Function(function) => format!("function `{function}`"),
            Self::Constructor { class, init } => format!("constructor `{class}::{init}`"),
            Self::Method { class, method } => format!("method `{class}::{method}`"),
        }
    }

    pub(crate) fn certificate_component(&self) -> String {
        match self {
            Self::Function(function) => format!("function.{function}"),
            Self::Constructor { class, init } => format!("constructor.{class}.{init}"),
            Self::Method { class, method } => format!("method.{class}.{method}"),
        }
    }
}

/// Semantic identity of the callable whose body contains a checked call.
///
/// The flavor is part of the identity. Source permits an initializer and a
/// method to share a member name, and their display spelling (`C::same`) is
/// therefore not sufficient to partition checker records by verified body.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum CallOwner {
    Function(String),
    Constructor { class: String, init: String },
    Method { class: String, method: String },
    Deinitializer { class: String },
}

impl CallOwner {
    pub(crate) fn render(&self) -> String {
        match self {
            Self::Function(function) => format!("function `{function}`"),
            Self::Constructor { class, init } => format!("constructor `{class}::{init}`"),
            Self::Method { class, method } => format!("method `{class}::{method}`"),
            Self::Deinitializer { class } => format!("destructor `{class}::deinit`"),
        }
    }

    /// Readable, flavor-preserving component of certificate source-map names.
    pub(crate) fn certificate_component(&self) -> String {
        match self {
            Self::Function(function) => format!("function.{function}"),
            Self::Constructor { class, init } => format!("constructor.{class}.{init}"),
            Self::Method { class, method } => format!("method.{class}.{method}"),
            Self::Deinitializer { class } => format!("deinitializer.{class}"),
        }
    }
}

/// Stable identity of a call inside one checked callable.
///
/// Source spans alone are not identities: monomorphization deliberately
/// preserves them.  The owner and resolved target make those clones distinct,
/// while duplicate insertion still fails closed if a future transform creates
/// an ambiguity inside one owner.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CallSiteKey {
    pub(crate) owner: CallOwner,
    pub(crate) span: Span,
    pub(crate) target: CallTarget,
}

/// The semantic effect a call grants to the callee.
///
/// This intentionally contains no symbolic binder names. The checker authors
/// it, VC generation reads it immutably on every symbolic visit to update
/// symbolic state, and the transition certificate adds only downstream
/// evidence about that update.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallEffect {
    SharedLoan,
    HavocUniqueBorrow,
}

/// Stage-neutral identity of one call transition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallTransition {
    pub(crate) place: Place,
    pub(crate) referent: Ty,
    pub(crate) effect: CallEffect,
    pub(crate) span: Span,
}

/// Complete checked passing mode for one resolved parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CallArgumentEffect {
    Value(ValueTransfer),
    Loan(CallTransition),
}

/// One checked argument, tied to its resolved callee parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallArgumentTransition {
    pub(crate) parameter_index: usize,
    pub(crate) parameter: String,
    pub(crate) parameter_ty: Ty,
    pub(crate) argument_span: Span,
    pub(crate) effect: CallArgumentEffect,
}

/// The implicit `self` loan of a method call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallReceiverTransition {
    pub(crate) class: String,
    pub(crate) transition: CallTransition,
}

/// Checker-authored effects for one call. Empty argument lists are retained:
/// their presence proves that this exact call was checked even when it has no
/// unique-borrow havoc to perform.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedCallTransition {
    pub(crate) key: CallSiteKey,
    pub(crate) receiver: Option<CallReceiverTransition>,
    pub(crate) arguments: Vec<CallArgumentTransition>,
}

/// Ephemeral checker-to-VC handoff for a single checked `Program`.
///
/// This is deliberately neither emitted nor serialized in module artifacts.
#[derive(Debug, Default)]
pub(crate) struct CheckedCallTransitions {
    by_site: HashMap<CallSiteKey, CheckedCallTransition>,
}

impl CheckedCallTransitions {
    pub(crate) fn insert(&mut self, call: CheckedCallTransition) -> Result<(), CallSiteKey> {
        let key = call.key.clone();
        match self.by_site.entry(key.clone()) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(call);
                Ok(())
            }
            std::collections::hash_map::Entry::Occupied(_) => Err(key),
        }
    }

    pub(crate) fn get(&self, key: &CallSiteKey) -> Option<&CheckedCallTransition> {
        self.by_site.get(key)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (&CallSiteKey, &CheckedCallTransition)> {
        self.by_site.iter()
    }

    pub(crate) fn for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&CallSiteKey, &CheckedCallTransition)> {
        self.by_site
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    pub(crate) fn for_owner_span(
        &self,
        owner: &CallOwner,
        span: Span,
    ) -> impl Iterator<Item = (&CallSiteKey, &CheckedCallTransition)> {
        self.by_site
            .iter()
            .filter(move |(key, _)| &key.owner == owner && key.span == span)
    }

    #[cfg(test)]
    pub(crate) fn get_mut(&mut self, key: &CallSiteKey) -> Option<&mut CheckedCallTransition> {
        self.by_site.get_mut(key)
    }
}

impl CallTransition {
    pub(crate) fn borrow(
        place: Place,
        mutability: Mutability,
        referent: Ty,
        span: Span,
    ) -> Result<Self, String> {
        let effect = match mutability {
            Mutability::Shared => CallEffect::SharedLoan,
            Mutability::Mut => CallEffect::HavocUniqueBorrow,
        };
        if matches!(referent, Ty::Slots(_)) {
            return Err(format!(
                "internal.call_transition.slots_unsupported: call loan for `{}` has owner-slot referent `{}`",
                place.render(),
                referent.name()
            ));
        }
        match &referent {
            Ty::Array(_) | Ty::Class(_) | Ty::Res(_) => Ok(Self {
                place,
                referent,
                effect,
                span,
            }),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Slots(_)
            | Ty::Borrow(..)
            | Ty::Unit => Err(format!(
                "internal.call_transition_unsupported: call loan for `{}` has \
                 unsupported referent `{}`",
                place.render(),
                referent.name()
            )),
        }
    }

    pub(crate) fn unique_borrow(place: Place, referent: Ty, span: Span) -> Result<Self, String> {
        Self::borrow(place, Mutability::Mut, referent, span)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CallHavocCertificateKind {
    /// A fresh class state or resource view was written back to its place.
    Writeback,
    /// An array additionally keeps the length of the pre-call sequence.
    Array { before: String, length_hyp: String },
}

/// Exact semantic payload of one fixed-proof transition certificate.
///
/// Slot certificates retain the immutable checker transition and the exact
/// control action that VC generation cross-validated before changing symbolic
/// state. They are deliberately distinct from [`CallTransition`]: admitting a
/// local `slot_take`/`slot_put` certificate does not admit owner slots to the
/// call ABI, and allocation/cleanup still have no certificate semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TransitionCertificateKind {
    CallHavoc {
        transition: CallTransition,
        fresh: String,
        observed: String,
        kind: CallHavocCertificateKind,
    },
    SlotTake {
        transition: CheckedSlotTransition,
        action: SlotAction,
        before: String,
        observed: String,
        index: String,
    },
    SlotPut {
        transition: CheckedSlotTransition,
        action: SlotAction,
        before: String,
        observed: String,
        index: String,
        staged: String,
    },
}

/// Evidence emitted for one selected symbolic transition.
///
/// Every term in the Lean predicate is copied from the live symbolic visit.
/// In particular, `observed` is read back from the generator environment
/// *after* place write-back; it is never the constructed update term reused as
/// if a write had necessarily succeeded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TransitionCertificate {
    pub(crate) name: String,
    pub(crate) thm_name: String,
    pub(crate) binders: Vec<(String, String)>,
    pub(crate) hyps: Vec<(String, String)>,
    pub(crate) kind: TransitionCertificateKind,
}

impl TransitionCertificate {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn call_havoc(
        name: String,
        thm_name: String,
        transition: CallTransition,
        fresh: String,
        observed: String,
        array_before: Option<String>,
        length_hyp: Option<String>,
        binders: Vec<(String, String)>,
        hyps: Vec<(String, String)>,
    ) -> Result<Self, String> {
        let place = transition.place.render();
        if transition.effect != CallEffect::HavocUniqueBorrow {
            return Err(format!(
                "internal.transition_certificate_shape: shared loan for `{place}` cannot produce a call-havoc certificate"
            ));
        }
        if !binders.iter().any(|(binder, _)| binder == &fresh) {
            return Err(format!(
                "internal.transition_certificate_missing_binder: call havoc for `{place}` \
                 did not retain its fresh binder `{fresh}`"
            ));
        }
        if observed.trim().is_empty() {
            return Err(format!(
                "internal.transition_certificate_missing_writeback: call havoc for `{place}` \
                 has no symbolic post-state"
            ));
        }

        let kind = match &transition.referent {
            Ty::Array(_) => {
                let before = array_before.ok_or_else(|| {
                    format!(
                        "internal.transition_certificate_missing_prestate: array call havoc for \
                         `{place}` has no symbolic pre-state"
                    )
                })?;
                let length_hyp = length_hyp.ok_or_else(|| {
                    format!(
                        "internal.transition_certificate_missing_length: array call havoc for \
                         `{place}` has no length-preservation fact"
                    )
                })?;
                let expected = format!("({fresh}.len) = ({before}.len)");
                match hyps.iter().find(|(hyp, _)| hyp == &length_hyp) {
                    Some((_, proposition)) if proposition == &expected => {}
                    Some((_, proposition)) => {
                        return Err(format!(
                            "internal.transition_certificate_bad_length: array call havoc for \
                             `{place}` recorded `{proposition}`, expected `{expected}`"
                        ));
                    }
                    None => {
                        return Err(format!(
                            "internal.transition_certificate_missing_length: array call havoc for \
                             `{place}` cannot find hypothesis `{length_hyp}`"
                        ));
                    }
                }
                CallHavocCertificateKind::Array { before, length_hyp }
            }
            Ty::Class(_) | Ty::Res(_) => {
                if array_before.is_some() || length_hyp.is_some() {
                    return Err(format!(
                        "internal.transition_certificate_shape: non-array call havoc for `{place}` \
                         carried array-only evidence"
                    ));
                }
                CallHavocCertificateKind::Writeback
            }
            Ty::Slots(_) => {
                return Err(format!(
                    "internal.transition_certificate.slots_unsupported: call havoc for `{place}` has owner-slot referent `{}`",
                    transition.referent.name()
                ));
            }
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Option(_)
            | Ty::OptionRaw(_)
            | Ty::Borrow(..)
            | Ty::Unit => {
                return Err(format!(
                    "internal.transition_certificate_unsupported: call havoc for `{place}` has \
                     unsupported referent `{}`",
                    transition.referent.name()
                ));
            }
        };

        Ok(Self {
            name,
            thm_name,
            binders,
            hyps,
            kind: TransitionCertificateKind::CallHavoc {
                transition,
                fresh,
                observed,
                kind,
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn slot_take(
        name: String,
        thm_name: String,
        transition: CheckedSlotTransition,
        action: SlotAction,
        before: String,
        observed: String,
        index: String,
        binders: Vec<(String, String)>,
    ) -> Result<Self, String> {
        let place = validate_slot_transition_action(&transition, &action, SlotCertificateOp::Take)?;
        require_slot_term(&before, &place, "pre-state")?;
        require_slot_term(&observed, &place, "observed post-state")?;
        require_slot_term(&index, &place, "index")?;
        Ok(Self {
            name,
            thm_name,
            binders,
            hyps: Vec::new(),
            kind: TransitionCertificateKind::SlotTake {
                transition,
                action,
                before,
                observed,
                index,
            },
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn slot_put(
        name: String,
        thm_name: String,
        transition: CheckedSlotTransition,
        action: SlotAction,
        before: String,
        observed: String,
        index: String,
        staged: String,
        binders: Vec<(String, String)>,
    ) -> Result<Self, String> {
        let place = validate_slot_transition_action(&transition, &action, SlotCertificateOp::Put)?;
        require_slot_term(&before, &place, "pre-state")?;
        require_slot_term(&observed, &place, "observed post-state")?;
        require_slot_term(&index, &place, "index")?;
        require_slot_term(&staged, &place, "staged payload")?;
        require_slot_binder(&binders, &staged, &place, "staged payload")?;
        Ok(Self {
            name,
            thm_name,
            binders,
            hyps: Vec::new(),
            kind: TransitionCertificateKind::SlotPut {
                transition,
                action,
                before,
                observed,
                index,
                staged,
            },
        })
    }

    pub(crate) fn place(&self) -> &Place {
        match &self.kind {
            TransitionCertificateKind::CallHavoc { transition, .. } => &transition.place,
            TransitionCertificateKind::SlotTake { transition, .. }
            | TransitionCertificateKind::SlotPut { transition, .. } => transition
                .container()
                .expect("slot take/put certificates always retain a container"),
        }
    }

    pub(crate) fn span(&self) -> Span {
        match &self.kind {
            TransitionCertificateKind::CallHavoc { transition, .. } => transition.span,
            TransitionCertificateKind::SlotTake { transition, .. }
            | TransitionCertificateKind::SlotPut { transition, .. } => transition.key.span,
        }
    }

    pub(crate) fn description(&self) -> &'static str {
        match &self.kind {
            TransitionCertificateKind::CallHavoc { .. } => "call-havoc",
            TransitionCertificateKind::SlotTake { .. } => "slot-take writeback",
            TransitionCertificateKind::SlotPut { .. } => "slot-put writeback",
        }
    }

    pub(crate) fn rejection_diagnostic_name(&self) -> &'static str {
        match &self.kind {
            TransitionCertificateKind::CallHavoc { .. } => {
                "internal.transition_certificate_rejected"
            }
            TransitionCertificateKind::SlotTake { .. }
            | TransitionCertificateKind::SlotPut { .. } => {
                "internal.slot_transition_certificate_rejected"
            }
        }
    }

    pub(crate) fn rejection_label(&self) -> String {
        match &self.kind {
            TransitionCertificateKind::CallHavoc { .. } => format!(
                "fresh symbolic state was not certified at `{}`",
                self.place().render()
            ),
            TransitionCertificateKind::SlotTake { .. }
            | TransitionCertificateKind::SlotPut { .. } => format!(
                "owner-slot write-back was not certified at `{}`",
                self.place().render()
            ),
        }
    }

    pub(crate) fn lean_goal(&self) -> String {
        match &self.kind {
            TransitionCertificateKind::CallHavoc {
                transition,
                fresh,
                observed,
                kind,
            } => match (transition.effect, kind) {
                (CallEffect::SharedLoan, _) => {
                    unreachable!("call_havoc rejects shared-loan certificates")
                }
                (CallEffect::HavocUniqueBorrow, CallHavocCertificateKind::Writeback) => {
                    format!("Sable.CallHavocWriteback ({fresh}) ({observed})")
                }
                (CallEffect::HavocUniqueBorrow, CallHavocCertificateKind::Array { before, .. }) => {
                    format!("Sable.ArrayCallHavoc ({before}) ({fresh}) ({observed})")
                }
            },
            TransitionCertificateKind::SlotTake {
                before,
                observed,
                index,
                ..
            } => format!("Sable.SlotTakeWriteback ({before}) ({observed}) ({index})"),
            TransitionCertificateKind::SlotPut {
                before,
                observed,
                index,
                staged,
                ..
            } => format!("Sable.SlotPutWriteback ({before}) ({observed}) ({index}) ({staged})"),
        }
    }

    pub(crate) fn lean_proof(&self) -> String {
        match &self.kind {
            TransitionCertificateKind::CallHavoc {
                kind: CallHavocCertificateKind::Writeback,
                ..
            } => "by exact ⟨rfl⟩".to_string(),
            TransitionCertificateKind::CallHavoc {
                kind: CallHavocCertificateKind::Array { length_hyp, .. },
                ..
            } => format!("by exact ⟨rfl, {length_hyp}⟩"),
            TransitionCertificateKind::SlotTake { .. }
            | TransitionCertificateKind::SlotPut { .. } => "by exact ⟨rfl⟩".to_string(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SlotCertificateOp {
    Take,
    Put,
}

fn validate_slot_transition_action(
    transition: &CheckedSlotTransition,
    action: &SlotAction,
    expected_op: SlotCertificateOp,
) -> Result<Place, String> {
    let Some(place) = transition.container().cloned() else {
        return Err(
            "internal.slot_transition_certificate_shape: slot allocation cannot produce a writeback certificate"
                .into(),
        );
    };
    let reject = |detail: &str| {
        format!(
            "internal.slot_transition_certificate_shape: checked owner-slot transition for `{}` {detail}",
            place.render()
        )
    };
    if action.span() != transition.key.span
        || action.effect_key() != &transition.key
        || action.op_span() != transition.op_span
        || action.payload() != &transition.payload
        || action.result_ty() != &transition.result_ty
    {
        return Err(reject("disagrees with its retained control action"));
    }
    let transition_op = match &transition.kind {
        CheckedSlotTransitionKind::Alloc { .. } => None,
        CheckedSlotTransitionKind::Take { .. } => Some(SlotCertificateOp::Take),
        CheckedSlotTransitionKind::Put { .. } => Some(SlotCertificateOp::Put),
    };
    let action_op = match action.kind() {
        SlotActionKind::Alloc { .. } => None,
        SlotActionKind::Take { .. } => Some(SlotCertificateOp::Take),
        SlotActionKind::Put { .. } => Some(SlotCertificateOp::Put),
    };
    if transition_op != Some(expected_op) || action_op != Some(expected_op) {
        return Err(reject(
            "has the wrong operation flavor for this certificate",
        ));
    }
    let shape_matches = match (&transition.kind, action.kind()) {
        (
            CheckedSlotTransitionKind::Take {
                container,
                container_span,
                index_span,
                ..
            },
            SlotActionKind::Take {
                container: action_container,
                container_span: action_container_span,
                index_span: action_index_span,
            },
        ) => {
            container == action_container
                && container_span == action_container_span
                && index_span == action_index_span
        }
        (
            CheckedSlotTransitionKind::Put {
                container,
                container_span,
                index_span,
                value_span,
                value_transfer,
                ..
            },
            SlotActionKind::Put {
                container: action_container,
                container_span: action_container_span,
                index_span: action_index_span,
                value_span: action_value_span,
                value_transfer: action_transfer,
                ..
            },
        ) => {
            container == action_container
                && container_span == action_container_span
                && index_span == action_index_span
                && value_span == action_value_span
                && value_transfer == action_transfer
        }
        (CheckedSlotTransitionKind::Alloc { .. }, SlotActionKind::Alloc { .. })
        | (CheckedSlotTransitionKind::Alloc { .. }, SlotActionKind::Take { .. })
        | (CheckedSlotTransitionKind::Alloc { .. }, SlotActionKind::Put { .. })
        | (CheckedSlotTransitionKind::Take { .. }, SlotActionKind::Alloc { .. })
        | (CheckedSlotTransitionKind::Take { .. }, SlotActionKind::Put { .. })
        | (CheckedSlotTransitionKind::Put { .. }, SlotActionKind::Alloc { .. })
        | (CheckedSlotTransitionKind::Put { .. }, SlotActionKind::Take { .. }) => false,
    };
    if !shape_matches {
        return Err(reject(
            "disagrees on its exact place, spans, or move transfer",
        ));
    }
    Ok(place)
}

fn require_slot_term(term: &str, place: &Place, role: &str) -> Result<(), String> {
    if term.trim().is_empty() {
        Err(format!(
            "internal.slot_transition_certificate_missing_term: `{}` has no {role}",
            place.render()
        ))
    } else {
        Ok(())
    }
}

fn require_slot_binder(
    binders: &[(String, String)],
    binder: &str,
    place: &Place,
    role: &str,
) -> Result<(), String> {
    if binders.iter().any(|(name, _)| name == binder) {
        Ok(())
    } else {
        Err(format!(
            "internal.slot_transition_certificate_missing_binder: `{}` cannot find {role} binder `{binder}`",
            place.render()
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::IntTy;

    #[test]
    fn call_transition_rejects_a_unique_borrow_shape_without_havoc_semantics() {
        let error = CallTransition::unique_borrow(Place::local("flag"), Ty::Bool, Span::new(0, 0))
            .expect_err("Boolean places are outside the admitted call-havoc slice");
        assert!(error.starts_with("internal.call_transition_unsupported:"));
    }

    #[test]
    fn owner_slots_never_acquire_call_havoc_transition_or_certificate_semantics() {
        let slots = Ty::slots(Ty::Int(IntTy::U64));
        let error = CallTransition::borrow(
            Place::local("cells"),
            Mutability::Mut,
            slots.clone(),
            Span::new(0, 1),
        )
        .expect_err("owner-slot borrows have no checked call-transition semantics yet");
        assert!(
            error.starts_with("internal.call_transition.slots_unsupported:"),
            "{error}"
        );

        // Forge the transition directly so the certificate gate is pinned
        // independently of the earlier checker-to-VC handoff refusal.
        let transition = CallTransition {
            place: Place::local("cells"),
            referent: slots,
            effect: CallEffect::HavocUniqueBorrow,
            span: Span::new(0, 1),
        };
        let error = TransitionCertificate::call_havoc(
            "transition.subject.call_havoc.cells".into(),
            "cert_transition_subject_call_havoc_cells".into(),
            transition,
            "_slots1".into(),
            "_slots1".into(),
            None,
            None,
            vec![("_slots1".into(), "Unsupported".into())],
            Vec::new(),
        )
        .expect_err("owner slots have no call-havoc certificate semantics");
        assert!(
            error.starts_with("internal.transition_certificate.slots_unsupported:"),
            "{error}"
        );
    }

    #[test]
    fn checked_call_table_rejects_a_duplicate_stable_identity() {
        let key = CallSiteKey {
            owner: CallOwner::Function("subject".into()),
            span: Span::new(10, 20),
            target: CallTarget::Function("mutate".into()),
        };
        let call = CheckedCallTransition {
            key: key.clone(),
            receiver: None,
            arguments: Vec::new(),
        };
        let mut calls = CheckedCallTransitions::default();
        calls
            .insert(call.clone())
            .expect("the first identity is unique");
        assert_eq!(calls.insert(call).expect_err("duplicates fail closed"), key);
        assert!(calls.get(&key).is_some(), "the first record is retained");
    }

    #[test]
    fn array_certificate_requires_the_exact_generated_length_fact() {
        let transition = CallTransition::unique_borrow(
            Place::local("values"),
            Ty::array(Ty::Int(IntTy::U64)),
            Span::new(0, 0),
        )
        .expect("arrays have call-havoc certificate semantics");
        let error = TransitionCertificate::call_havoc(
            "transition.subject.call_havoc.values".into(),
            "cert_transition_subject_call_havoc_values".into(),
            transition,
            "_arr1".into(),
            "_arr1".into(),
            Some("values".into()),
            Some("h_values_len".into()),
            vec![
                ("values".into(), "Sable.Seq Int".into()),
                ("_arr1".into(), "Sable.Seq Int".into()),
            ],
            vec![("h_values_len".into(), "(_arr1.len) = (other.len)".into())],
        )
        .expect_err("a length fact about another pre-state must fail closed");
        assert!(error.starts_with("internal.transition_certificate_bad_length:"));
    }
}
