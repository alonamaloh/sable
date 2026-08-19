//! Checker-authored ownership and mutation facts for one checked AST.
//!
//! `Place` answers which storage a source expression names. This module is
//! the next layer up: it records what an admitted semantic boundary does with
//! that place. Records are ephemeral and contain no Lean binders or cleanup
//! actions.

#![deny(clippy::wildcard_enum_match_arm)]

use crate::ast::{DeviceOp, Mutability, RawOp, ResOp, Ty};
use crate::place::Place;
use crate::span::Span;
use crate::transition::{CallArgumentEffect, CallOwner, CheckedCallTransitions};
use std::collections::HashMap;

/// Whether a by-value expression copies an existing value, moves an existing
/// owner, or transfers a fresh temporary with no source place to invalidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValueTransferKind {
    Copy,
    Move,
    Fresh,
}

/// The checker's flow-sensitive answer for one by-value transfer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ValueTransfer {
    pub(crate) source: Option<Place>,
    pub(crate) value_ty: Ty,
    pub(crate) kind: ValueTransferKind,
    pub(crate) carried_obligation: bool,
    pub(crate) branded: bool,
    pub(crate) span: Span,
}

/// Stable semantic identity of the sink receiving a non-call value.
///
/// Expression spans are insufficient because parser desugaring deliberately
/// reuses source anchors (a `for` initializer and increment may both point at
/// the keyword). The destination/role distinguishes those boundaries without
/// depending on traversal order.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ValueTransferSink {
    Binding(String),
    Assignment(Place),
    Return,
    FieldAssignment(Place),
    DiscardTemporary,
    SystemDeallocResource,
    SystemDeallocRelease,
    OptionPayload,
    SlotPut(Place),
}

impl ValueTransferSink {
    pub(crate) fn render(&self) -> String {
        match self {
            Self::Binding(binding) => format!("binding.{binding}"),
            Self::Assignment(place) => format!("assignment.{}", place.render()),
            Self::Return => "return".into(),
            Self::FieldAssignment(place) => format!("field.{}", place.render()),
            Self::DiscardTemporary => "discard_temporary".into(),
            Self::SystemDeallocResource => "system_dealloc.resource".into(),
            Self::SystemDeallocRelease => "system_dealloc.release".into(),
            Self::OptionPayload => "option.payload".into(),
            Self::SlotPut(place) => format!("slot_put.{}", place.render()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ValueTransferKey {
    pub(crate) owner: CallOwner,
    pub(crate) span: Span,
    pub(crate) sink: ValueTransferSink,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct EffectSiteKey {
    pub(crate) owner: CallOwner,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedOptionTake {
    pub(crate) key: EffectSiteKey,
    pub(crate) source: Place,
    pub(crate) source_span: Span,
    pub(crate) payload: Ty,
}

/// The exact semantic flavor of one admitted owner-slot transition.
///
/// The source AST keeps the surface [`crate::ast::SlotOp`]. This enum keeps
/// the checker's resolved boundary: allocation has no container place, while
/// take and put mutate one exact owner. Put additionally links the value move
/// recorded at the same boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CheckedSlotTransitionKind {
    Alloc {
        length_ty: Ty,
        length_span: Span,
    },
    Take {
        container: Place,
        container_span: Span,
        index_ty: Ty,
        index_span: Span,
    },
    Put {
        container: Place,
        container_span: Span,
        index_ty: Ty,
        index_span: Span,
        value_span: Span,
        value_transfer: ValueTransferKey,
    },
}

/// Checker-authored owner-slot transition for one exact source operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedSlotTransition {
    pub(crate) key: EffectSiteKey,
    pub(crate) op_span: Span,
    pub(crate) payload: Ty,
    pub(crate) result_ty: Ty,
    pub(crate) kind: CheckedSlotTransitionKind,
}

impl CheckedSlotTransition {
    pub(crate) fn container(&self) -> Option<&Place> {
        match &self.kind {
            CheckedSlotTransitionKind::Alloc { .. } => None,
            CheckedSlotTransitionKind::Take { container, .. }
            | CheckedSlotTransitionKind::Put { container, .. } => Some(container),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedExposure {
    pub(crate) key: EffectSiteKey,
    pub(crate) owner_place: Place,
    pub(crate) owner_span: Span,
    pub(crate) owner_ty: Ty,
    pub(crate) mutability: Mutability,
    pub(crate) pointer: String,
    pub(crate) pointer_span: Span,
    pub(crate) resource: String,
    pub(crate) resource_span: Span,
}

/// Flavor-preserving identity of one sealed compiler operation. Keeping the
/// resolved enum variant in the checker handoff prevents VC generation from
/// selecting an ownership rule by re-decoding a source spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckedSealedTarget {
    Raw(RawOp),
    Resource(ResOp),
    Device(DeviceOp),
}

impl CheckedSealedTarget {
    pub(crate) fn render(self) -> &'static str {
        match self {
            Self::Raw(op) => op.name(),
            Self::Resource(op) => op.name(),
            Self::Device(op) => op.name(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedSealedArgument {
    pub(crate) index: usize,
    pub(crate) argument_ty: Ty,
    pub(crate) argument_span: Span,
    pub(crate) effect: CallArgumentEffect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedSealedOperation {
    pub(crate) key: EffectSiteKey,
    pub(crate) target: CheckedSealedTarget,
    pub(crate) arguments: Vec<CheckedSealedArgument>,
    pub(crate) result_ty: Ty,
}

/// One semantic mutation that a loop iteration may perform. Variants retain
/// the checker fact that justified the mutation instead of flattening every
/// effect to a source name; VC generation currently consumes their canonical
/// places for havoc and may consume the richer payload later.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CheckedMutation {
    DirectWrite {
        place: Place,
    },
    UniqueLoan(crate::transition::CallTransition),
    OptionTake {
        source: Place,
        payload: Ty,
    },
    Slot {
        key: EffectSiteKey,
        operation: CheckedSlotMutationKind,
        container: Place,
        payload: Ty,
    },
    ExposureRebuild {
        owner_place: Place,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CheckedSlotMutationKind {
    Take,
    Put,
}

impl CheckedMutation {
    pub(crate) fn place(&self) -> &Place {
        match self {
            Self::DirectWrite { place } => place,
            Self::UniqueLoan(transition) => &transition.place,
            Self::OptionTake { source, .. } => source,
            Self::Slot { container, .. } => container,
            Self::ExposureRebuild { owner_place } => owner_place,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CheckedLoopEffects {
    pub(crate) key: EffectSiteKey,
    pub(crate) condition_span: Span,
    pub(crate) mutations: Vec<CheckedMutation>,
}

/// One checker-sealed ownership/mutation plan for the exact typed program.
#[derive(Debug, Default)]
pub(crate) struct CheckedOwnershipPlan {
    pub(crate) calls: CheckedCallTransitions,
    option_takes: HashMap<EffectSiteKey, CheckedOptionTake>,
    slot_transitions: HashMap<EffectSiteKey, CheckedSlotTransition>,
    exposures: HashMap<EffectSiteKey, CheckedExposure>,
    sealed_operations: HashMap<EffectSiteKey, CheckedSealedOperation>,
    loops: HashMap<EffectSiteKey, CheckedLoopEffects>,
    value_transfers: HashMap<ValueTransferKey, ValueTransfer>,
}

impl CheckedOwnershipPlan {
    pub(crate) fn insert_option_take(
        &mut self,
        effect: CheckedOptionTake,
    ) -> Result<(), EffectSiteKey> {
        insert_exact(&mut self.option_takes, effect.key.clone(), effect)
    }

    pub(crate) fn option_take(&self, key: &EffectSiteKey) -> Option<&CheckedOptionTake> {
        self.option_takes.get(key)
    }

    pub(crate) fn option_takes_for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&EffectSiteKey, &CheckedOptionTake)> {
        self.option_takes
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    pub(crate) fn insert_slot_transition(
        &mut self,
        transition: CheckedSlotTransition,
    ) -> Result<(), EffectSiteKey> {
        insert_exact(
            &mut self.slot_transitions,
            transition.key.clone(),
            transition,
        )
    }

    pub(crate) fn slot_transition(&self, key: &EffectSiteKey) -> Option<&CheckedSlotTransition> {
        self.slot_transitions.get(key)
    }

    pub(crate) fn slot_transitions_for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&EffectSiteKey, &CheckedSlotTransition)> {
        self.slot_transitions
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    pub(crate) fn insert_exposure(&mut self, effect: CheckedExposure) -> Result<(), EffectSiteKey> {
        insert_exact(&mut self.exposures, effect.key.clone(), effect)
    }

    pub(crate) fn exposure(&self, key: &EffectSiteKey) -> Option<&CheckedExposure> {
        self.exposures.get(key)
    }

    pub(crate) fn exposures_for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&EffectSiteKey, &CheckedExposure)> {
        self.exposures
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    pub(crate) fn insert_sealed_operation(
        &mut self,
        operation: CheckedSealedOperation,
    ) -> Result<(), EffectSiteKey> {
        insert_exact(
            &mut self.sealed_operations,
            operation.key.clone(),
            operation,
        )
    }

    pub(crate) fn sealed_operation(&self, key: &EffectSiteKey) -> Option<&CheckedSealedOperation> {
        self.sealed_operations.get(key)
    }

    pub(crate) fn sealed_operations_for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&EffectSiteKey, &CheckedSealedOperation)> {
        self.sealed_operations
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    pub(crate) fn insert_loop(&mut self, effects: CheckedLoopEffects) -> Result<(), EffectSiteKey> {
        insert_exact(&mut self.loops, effects.key.clone(), effects)
    }

    pub(crate) fn loop_effects(&self, key: &EffectSiteKey) -> Option<&CheckedLoopEffects> {
        self.loops.get(key)
    }

    pub(crate) fn loops_for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&EffectSiteKey, &CheckedLoopEffects)> {
        self.loops
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    pub(crate) fn insert_value_transfer(
        &mut self,
        owner: CallOwner,
        sink: ValueTransferSink,
        transfer: ValueTransfer,
    ) -> Result<(), ValueTransferKey> {
        let key = ValueTransferKey {
            owner,
            span: transfer.span,
            sink,
        };
        insert_exact(&mut self.value_transfers, key.clone(), transfer)
    }

    pub(crate) fn value_transfer(&self, key: &ValueTransferKey) -> Option<&ValueTransfer> {
        self.value_transfers.get(key)
    }

    pub(crate) fn value_transfers_for_owner(
        &self,
        owner: &CallOwner,
    ) -> impl Iterator<Item = (&ValueTransferKey, &ValueTransfer)> {
        self.value_transfers
            .iter()
            .filter(move |(key, _)| &key.owner == owner)
    }

    #[cfg(test)]
    pub(crate) fn option_take_mut(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<&mut CheckedOptionTake> {
        self.option_takes.get_mut(key)
    }

    #[cfg(test)]
    pub(crate) fn remove_option_take(&mut self, key: &EffectSiteKey) -> Option<CheckedOptionTake> {
        self.option_takes.remove(key)
    }

    #[cfg(test)]
    pub(crate) fn slot_transition_mut(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<&mut CheckedSlotTransition> {
        self.slot_transitions.get_mut(key)
    }

    #[cfg(test)]
    pub(crate) fn remove_slot_transition(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<CheckedSlotTransition> {
        self.slot_transitions.remove(key)
    }

    #[cfg(test)]
    pub(crate) fn exposure_mut(&mut self, key: &EffectSiteKey) -> Option<&mut CheckedExposure> {
        self.exposures.get_mut(key)
    }

    #[cfg(test)]
    pub(crate) fn remove_exposure(&mut self, key: &EffectSiteKey) -> Option<CheckedExposure> {
        self.exposures.remove(key)
    }

    #[cfg(test)]
    pub(crate) fn sealed_operation_mut(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<&mut CheckedSealedOperation> {
        self.sealed_operations.get_mut(key)
    }

    #[cfg(test)]
    pub(crate) fn remove_sealed_operation(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<CheckedSealedOperation> {
        self.sealed_operations.remove(key)
    }

    #[cfg(test)]
    pub(crate) fn loop_effects_mut(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<&mut CheckedLoopEffects> {
        self.loops.get_mut(key)
    }

    #[cfg(test)]
    pub(crate) fn remove_loop_effects(
        &mut self,
        key: &EffectSiteKey,
    ) -> Option<CheckedLoopEffects> {
        self.loops.remove(key)
    }

    #[cfg(test)]
    pub(crate) fn value_transfer_mut(
        &mut self,
        key: &ValueTransferKey,
    ) -> Option<&mut ValueTransfer> {
        self.value_transfers.get_mut(key)
    }

    #[cfg(test)]
    pub(crate) fn remove_value_transfer(
        &mut self,
        key: &ValueTransferKey,
    ) -> Option<ValueTransfer> {
        self.value_transfers.remove(key)
    }
}

fn insert_exact<K: Clone + Eq + std::hash::Hash, T>(
    table: &mut HashMap<K, T>,
    key: K,
    value: T,
) -> Result<(), K> {
    match table.entry(key.clone()) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(value);
            Ok(())
        }
        std::collections::hash_map::Entry::Occupied(_) => Err(key),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key() -> EffectSiteKey {
        EffectSiteKey {
            owner: CallOwner::Function("subject".into()),
            span: Span::new(10, 20),
        }
    }

    #[test]
    fn ownership_tables_reject_duplicate_effect_site_identities() {
        let mut plan = CheckedOwnershipPlan::default();

        let option_take = CheckedOptionTake {
            key: key(),
            source: Place::local("pending"),
            source_span: Span::new(10, 17),
            payload: Ty::Bool,
        };
        plan.insert_option_take(option_take.clone())
            .expect("the first option-take identity is unique");
        assert_eq!(
            plan.insert_option_take(option_take)
                .expect_err("duplicate option-take identities fail closed"),
            key()
        );

        let slot_transition = CheckedSlotTransition {
            key: key(),
            op_span: Span::new(10, 15),
            payload: Ty::Int(crate::ast::IntTy::U64),
            result_ty: Ty::slots(Ty::Int(crate::ast::IntTy::U64)),
            kind: CheckedSlotTransitionKind::Alloc {
                length_ty: Ty::Int(crate::ast::IntTy::U64),
                length_span: Span::new(16, 17),
            },
        };
        plan.insert_slot_transition(slot_transition.clone())
            .expect("the first slot-transition identity is unique");
        assert_eq!(
            plan.insert_slot_transition(slot_transition)
                .expect_err("duplicate slot-transition identities fail closed"),
            key()
        );

        let exposure = CheckedExposure {
            key: key(),
            owner_place: Place::local("bytes"),
            owner_span: Span::new(10, 15),
            owner_ty: Ty::array(Ty::Bool),
            mutability: Mutability::Mut,
            pointer: "pointer".into(),
            pointer_span: Span::new(16, 17),
            resource: "memory".into(),
            resource_span: Span::new(18, 19),
        };
        plan.insert_exposure(exposure.clone())
            .expect("the first exposure identity is unique");
        assert_eq!(
            plan.insert_exposure(exposure)
                .expect_err("duplicate exposure identities fail closed"),
            key()
        );

        let sealed = CheckedSealedOperation {
            key: key(),
            target: CheckedSealedTarget::Resource(ResOp::Join),
            arguments: Vec::new(),
            result_ty: Ty::Unit,
        };
        plan.insert_sealed_operation(sealed.clone())
            .expect("the first sealed-operation identity is unique");
        assert_eq!(
            plan.insert_sealed_operation(sealed)
                .expect_err("duplicate sealed-operation identities fail closed"),
            key()
        );

        let loop_effects = CheckedLoopEffects {
            key: key(),
            condition_span: Span::new(11, 19),
            mutations: Vec::new(),
        };
        plan.insert_loop(loop_effects.clone())
            .expect("the first loop identity is unique");
        assert_eq!(
            plan.insert_loop(loop_effects)
                .expect_err("duplicate loop identities fail closed"),
            key()
        );

        let transfer = ValueTransfer {
            source: Some(Place::local("value")),
            value_ty: Ty::Bool,
            kind: ValueTransferKind::Copy,
            carried_obligation: false,
            branded: false,
            span: key().span,
        };
        plan.insert_value_transfer(
            key().owner,
            ValueTransferSink::Binding("copy".into()),
            transfer.clone(),
        )
        .expect("the first value-transfer identity is unique");
        plan.insert_value_transfer(
            key().owner,
            ValueTransferSink::Assignment(Place::local("copy")),
            transfer.clone(),
        )
        .expect("one source anchor may feed a distinct desugared sink");
        assert_eq!(
            plan.insert_value_transfer(
                key().owner,
                ValueTransferSink::Binding("copy".into()),
                transfer,
            )
            .expect_err("duplicate value-transfer identities fail closed"),
            ValueTransferKey {
                owner: key().owner,
                span: key().span,
                sink: ValueTransferSink::Binding("copy".into()),
            }
        );
    }
}
