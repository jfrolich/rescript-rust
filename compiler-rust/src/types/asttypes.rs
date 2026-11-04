//! Auxiliary AST types used by parsetree and typedtree.
//!
//! These types are shared between the surface syntax (Parsetree) and
//! the typed syntax (Typedtree).

use super::decl_loc::DeclLoc;
use crate::location::Location;
use serde::{Deserialize, Serialize};
use smol_str::SmolStr;

/// Private/public flag for type definitions.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Default,
)]
pub enum PrivateFlag {
    /// Private type (cannot be constructed outside the module)
    Private,
    /// Public type
    #[default]
    Public,
}

/// Mutable/immutable flag for record fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum MutableFlag {
    /// Immutable field
    #[default]
    Immutable,
    /// Mutable field
    Mutable,
}

/// A label (field name, method name, etc.).
pub type Label = SmolStr;

/// Argument label for function parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum ArgLabel {
    /// No label: `x => ...`
    #[default]
    Nolabel,
    /// Labeled argument: `~label => ...`
    Labelled(Located<String, DeclLoc>),
    /// Optional argument: `~(label=e) => ...`
    Optional(Located<String, DeclLoc>),
}

impl ArgLabel {
    /// Create a labeled argument.
    pub fn labelled(name: impl Into<String>, loc: DeclLoc) -> Self {
        ArgLabel::Labelled(Located {
            txt: name.into(),
            loc,
        })
    }

    /// Create an optional argument.
    pub fn optional(name: impl Into<String>, loc: DeclLoc) -> Self {
        ArgLabel::Optional(Located {
            txt: name.into(),
            loc,
        })
    }

    /// Create a labeled argument with no location.
    #[cfg(test)]
    pub fn labelled_noloc(name: impl Into<String>) -> Self {
        ArgLabel::Labelled(Located {
            txt: name.into(),
            loc: DeclLoc::none(),
        })
    }

    /// Create an optional argument with no location.
    #[cfg(test)]
    pub fn optional_noloc(name: impl Into<String>) -> Self {
        ArgLabel::Optional(Located {
            txt: name.into(),
            loc: DeclLoc::none(),
        })
    }

    /// Get the label name, if any.
    pub fn label_name(&self) -> Option<&str> {
        match self {
            ArgLabel::Nolabel => None,
            ArgLabel::Labelled(l) => Some(&l.txt),
            ArgLabel::Optional(l) => Some(&l.txt),
        }
    }

    /// Check if this is a labeled (non-optional) argument.
    pub fn is_labelled(&self) -> bool {
        matches!(self, ArgLabel::Labelled(_))
    }

    /// Check if this is an optional argument.
    pub fn is_optional(&self) -> bool {
        matches!(self, ArgLabel::Optional(_))
    }

    /// Get the location of the label, if any.
    pub fn loc(&self) -> DeclLoc {
        match self {
            ArgLabel::Nolabel => DeclLoc::none(),
            ArgLabel::Labelled(l) => l.loc,
            ArgLabel::Optional(l) => l.loc,
        }
    }

    /// Check if two arg labels have the same label name.
    pub fn same_label(&self, other: &ArgLabel) -> bool {
        match (self, other) {
            (ArgLabel::Nolabel, ArgLabel::Nolabel) => true,
            (ArgLabel::Labelled(l1), ArgLabel::Labelled(l2)) => l1.txt == l2.txt,
            (ArgLabel::Optional(l1), ArgLabel::Optional(l2)) => l1.txt == l2.txt,
            _ => false,
        }
    }
}

/// A value with source location. Declarations and type labels locate their
/// names with a [`DeclLoc`] handle (see `types::decl_loc`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Located<T, L = Location> {
    /// The value.
    pub txt: T,
    /// The source location.
    pub loc: L,
}

impl<T, L: Copy + Default> Located<T, L> {
    /// Create a new located value.
    pub fn new(txt: T, loc: L) -> Self {
        Located { txt, loc }
    }

    /// Create a located value with no location.
    pub fn noloc(txt: T) -> Self {
        Located {
            txt,
            loc: L::default(),
        }
    }

    /// Map a function over the contained value.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Located<U, L> {
        Located {
            txt: f(self.txt),
            loc: self.loc,
        }
    }

    /// Get a reference to the contained value.
    pub fn as_ref(&self) -> Located<&T, L> {
        Located {
            txt: &self.txt,
            loc: self.loc,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arg_label() {
        let nolabel = ArgLabel::Nolabel;
        assert!(nolabel.label_name().is_none());

        let labelled = ArgLabel::labelled_noloc("foo");
        assert_eq!(labelled.label_name(), Some("foo"));
        assert!(labelled.is_labelled());

        let optional = ArgLabel::optional_noloc("bar");
        assert_eq!(optional.label_name(), Some("bar"));
        assert!(optional.is_optional());
    }

    #[test]
    fn test_same_label() {
        let l1 = ArgLabel::labelled_noloc("x");
        let l2 = ArgLabel::labelled_noloc("x");
        let l3 = ArgLabel::labelled_noloc("y");
        let o1 = ArgLabel::optional_noloc("x");

        assert!(l1.same_label(&l2));
        assert!(!l1.same_label(&l3));
        assert!(!l1.same_label(&o1)); // Labelled vs Optional
    }

    #[test]
    fn test_located() {
        let loc: Located<i32> = Located::new(42, Location::none());
        assert_eq!(loc.txt, 42);

        let mapped = loc.map(|x| x * 2);
        assert_eq!(mapped.txt, 84);
    }

    #[test]
    fn test_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<ArgLabel>();
        assert_send_sync::<Located<String>>();
    }

    #[test]
    fn type_labels_hold_compact_locations() {
        assert_eq!(std::mem::size_of::<Located<String, DeclLoc>>(), 32);
        assert_eq!(std::mem::size_of::<ArgLabel>(), 32);
    }
}
