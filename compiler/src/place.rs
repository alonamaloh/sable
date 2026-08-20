//! Semantic identities for owned and borrowed storage.
//!
//! The checker tracks moves and call conflicts by place, while VC generation
//! writes fresh call state back to the place an argument lends.  Both must
//! decode source expressions to the same root-and-projection identity: a
//! disagreement can leave the checker protecting one place while VCgen havocs
//! another.  This module is the single structural answer shared by those
//! stages.

use crate::ast::{Expr, ExprKind, Mutability};

/// A local (including `self`), optionally projected through fields.
///
/// Fields remain a vector even though today's expression AST carries at most
/// one projection.  Containment and overlap are defined for arbitrary paths,
/// so adding a nested projection cannot silently degrade them to name tests.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Place {
    root: String,
    fields: Vec<String>,
}

impl Place {
    pub(crate) fn local(name: &str) -> Self {
        Self {
            root: name.to_string(),
            fields: Vec::new(),
        }
    }

    pub(crate) fn field(root: &str, field: &str) -> Self {
        Self::local(root).project(field)
    }

    fn project(mut self, field: &str) -> Self {
        self.fields.push(field.to_string());
        self
    }

    /// The source place consumed by a by-value expression, if it has one.
    ///
    /// Calls and constructors are temporaries, and ordinary field reads are
    /// copy-only today.  A bare name and `self.f` are the two forms whose
    /// authority can leave a source place (ADR 0030).
    pub(crate) fn from_value_expr(expr: &Expr) -> Option<Self> {
        match &expr.kind {
            ExprKind::Var(name) => Some(Self::local(name)),
            ExprKind::SelfField { field } => Some(Self::field("self", field)),
            _ => None,
        }
    }

    pub(crate) fn root(&self) -> &str {
        &self.root
    }

    /// Structural field-path components, in projection order.
    ///
    /// Certificate encoders consume this slice directly. Re-parsing
    /// [`Place::render`] would collapse the shared storage identity back into
    /// punctuation-sensitive text at exactly the boundary the certificate is
    /// meant to audit.
    pub(crate) fn fields(&self) -> &[String] {
        &self.fields
    }

    pub(crate) fn is_root(&self) -> bool {
        self.fields.is_empty()
    }

    /// The sole field projection, for AST paths that are currently limited to
    /// one.  A caller that cannot handle deeper paths must reject `None` when
    /// [`Place::is_root`] is false rather than truncate the place.
    pub(crate) fn direct_field(&self) -> Option<&str> {
        match self.fields.as_slice() {
            [field] => Some(field),
            _ => None,
        }
    }

    /// `self` contains `other`: same root, and `self`'s field path is a
    /// prefix of `other`'s. `o` contains `o.inner`; not conversely.
    pub(crate) fn contains(&self, other: &Self) -> bool {
        self.root == other.root
            && self.fields.len() <= other.fields.len()
            && self.fields[..] == other.fields[..self.fields.len()]
    }

    /// Two places overlap when either contains the other. `o` overlaps
    /// `o.inner`; `o.a` and `o.b` do not.
    pub(crate) fn overlaps(&self, other: &Self) -> bool {
        self.contains(other) || other.contains(self)
    }

    pub(crate) fn render(&self) -> String {
        let mut rendered = self.root.clone();
        for field in &self.fields {
            rendered.push('.');
            rendered.push_str(field);
        }
        rendered
    }

    /// The source-name-keyed flow/symbolic-state entry for this place.
    ///
    /// Fields of `self` are pseudo-variables such as `self.f`, so callers must
    /// never substitute the root alone at this boundary.
    pub(crate) fn state_key(&self) -> String {
        self.render()
    }

    /// A stable source-derived fragment for fresh binder names.
    pub(crate) fn binder_hint(&self) -> String {
        let mut hint = self.root.clone();
        for field in &self.fields {
            hint.push('_');
            hint.push_str(field);
        }
        hint
    }
}

/// An explicit source borrow and the exact place it lends.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct BorrowedPlace {
    place: Place,
    mutability: Mutability,
}

impl BorrowedPlace {
    pub(crate) fn from_expr(expr: &Expr) -> Option<Self> {
        let ExprKind::Borrow {
            array,
            field,
            mutable,
        } = &expr.kind
        else {
            return None;
        };
        let place = field
            .as_deref()
            .map_or_else(|| Place::local(array), |field| Place::field(array, field));
        let mutability = if *mutable {
            Mutability::Mut
        } else {
            Mutability::Shared
        };
        Some(Self { place, mutability })
    }

    pub(crate) fn place(&self) -> &Place {
        &self.place
    }

    pub(crate) fn into_place(self) -> Place {
        self.place
    }

    pub(crate) fn mutability(&self) -> Mutability {
        self.mutability
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::Span;

    fn expr(kind: ExprKind) -> Expr {
        Expr {
            kind,
            span: Span::new(0, 0),
            ty: None,
        }
    }

    #[test]
    fn containment_and_overlap_follow_projection_prefixes() {
        let object = Place::local("object");
        let left = object.clone().project("left");
        let left_leaf = left.clone().project("leaf");
        let right = object.clone().project("right");

        assert!(object.contains(&left_leaf));
        assert!(left.contains(&left_leaf));
        assert!(!left_leaf.contains(&left));
        assert!(object.overlaps(&right));
        assert!(!left.overlaps(&right));
        assert_eq!(left_leaf.state_key(), "object.left.leaf");
        assert_eq!(left_leaf.binder_hint(), "object_left_leaf");
    }

    #[test]
    fn value_and_borrow_syntax_resolve_to_the_same_place() {
        let value = expr(ExprKind::SelfField {
            field: "memory".into(),
        });
        let borrow = expr(ExprKind::Borrow {
            array: "self".into(),
            field: Some("memory".into()),
            mutable: true,
        });

        let value_place = Place::from_value_expr(&value).expect("field value has a place");
        let borrowed = BorrowedPlace::from_expr(&borrow).expect("borrow has a place");
        assert_eq!(value_place, *borrowed.place());
        assert_eq!(borrowed.mutability(), Mutability::Mut);
        assert_eq!(borrowed.place().root(), "self");
        assert_eq!(borrowed.place().direct_field(), Some("memory"));
    }

    #[test]
    fn temporaries_and_non_borrows_do_not_acquire_places() {
        let literal = expr(ExprKind::IntLit(1));
        assert!(Place::from_value_expr(&literal).is_none());
        assert!(BorrowedPlace::from_expr(&literal).is_none());
    }
}
