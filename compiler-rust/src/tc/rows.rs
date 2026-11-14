//! R3 skeleton: the descriptors a 16-byte node does not hold (objects and
//! their fields, polymorphic variant rows, universal variables, polymorphic
//! types, packages) in worker-local pools, and their unification. Built by
//! slices R3e to R3h (CHECKER_REWRITE.md, "R3 as designed").
//!
//! The layout is the published one (tc/segment.rs, `ExtraDescriptor`): an
//! extended node is `TUPLE | EXTENDED`, `a` indexes [`Extras::descriptors`]
//! and the children are the node's list slots. A graph made from a segment
//! starts with the segment's rows copied ([`Extras::from_segment`]), so the
//! indices of frozen nodes stay valid; rows made during a check are appended.

use super::graph::Ty;
use super::segment::{ExtraDescriptor, PackageRow, RowFieldRow, Segment, VariantRow};
use super::unify::{Checker, Clash};

/// Worker-local descriptor pools, cleared between units.
#[derive(Default)]
pub struct Extras {
    pub descriptors: Vec<ExtraDescriptor>,
    pub variants: Vec<VariantRow>,
    pub row_fields: Vec<RowFieldRow>,
    pub packages: Vec<PackageRow>,
    /// Field mutability cells; a cell is a link to another when its high bit
    /// is set (`unify_mutability`, types/ctype.rs:9580).
    pub mutabilities: Vec<u32>,
}

/// One field of a flattened object or row, on the walk's stack: 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct FieldRef {
    pub name: u32,
    /// The `Tfield` node, or the row-field index for a variant.
    pub at: u32,
    pub ty: Ty,
}

impl Extras {
    /// O(rows of the segment): one bulk copy per pool; a frozen mutability
    /// cell holds its value and links to nothing. The indices of a
    /// segment's rows are the indices here, so the nodes of an instance
    /// name their descriptors without translation.
    pub fn from_segment(segment: &Segment) -> Extras {
        let pools = &segment.signature;
        Extras {
            descriptors: pools.descriptor_extras.to_vec(),
            variants: pools.variants.to_vec(),
            row_fields: pools.row_fields.to_vec(),
            packages: pools.packages.to_vec(),
            mutabilities: pools.mutabilities.iter().map(|&mutable| u32::from(mutable)).collect(),
        }
    }
}

impl Checker {
    /// `flatten_fields` (compiler/ml/ctype.ml:314): append the fields of an
    /// object to `out` in list order and return the rest (a variable or
    /// `Tnil`). O(fields), no allocation beyond `out`'s growth. (R3e)
    pub fn flatten_fields(&mut self, object: Ty, out: &mut Vec<FieldRef>) -> Ty {
        todo!("R3e")
    }

    /// `unify_fields` (compiler/ml/ctype.ml:2467-2539): associate the two
    /// field lists by name (`associate_fields`, ctype.ml:330), unify the
    /// rests with fresh rows for the fields each side lacks, then the common
    /// fields' mutability and types, in OCaml's order. O(fields log fields)
    /// for the association (both lists are sorted once) plus one pushed pair
    /// per common field. (R3e)
    pub fn unify_fields(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3e")
    }

    /// `unify_row` (compiler/ml/ctype.ml:2541-2641): merge the two rows'
    /// fields (`merge_row_fields`, ctype.ml:380), decide closedness and the
    /// row name, link the two `more` variables to a fresh row, then
    /// [`Checker::unify_row_field`] for each common tag. O(tags log tags)
    /// plus the fields. (R3f)
    pub fn unify_row(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3f")
    }

    /// `unify_row_field` (compiler/ml/ctype.ml:2643-2730): one common tag of
    /// two rows. O(types of the two fields). (R3f)
    pub fn unify_row_field(
        &mut self,
        fixed_left: bool,
        fixed_right: bool,
        more: Ty,
        left: u32,
        right: u32,
    ) -> Result<(), Clash> {
        todo!("R3f")
    }

    /// `unify_univar` (compiler/ml/ctype.ml:1544-1561): two universal
    /// variables are equal only when the innermost scope that binds either
    /// pairs them. O(scopes × bound variables). (R3g)
    pub fn unify_univar(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `enter_poly` (compiler/ml/ctype.ml:1656-1686): pair the bound
    /// variables of two polymorphic types for the unification of their
    /// bodies, and check afterwards that none escaped
    /// (`univars_escape`, ctype.ml:1626). Pushes the body pair and a
    /// `LeavePoly` frame. O(bound variables) plus the escape walk. (R3g)
    pub fn enter_poly(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `occur_univar` (compiler/ml/ctype.ml:1563-1624): no universal
    /// variable of `ty` is free of its binder. O(nodes), marks, explicit
    /// stack; O(1) when the unit has made no universal variable. (R3g)
    pub fn occur_univar(&mut self, ty: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `unify_package` (compiler/ml/ctype.ml:2172-2203): two packages of
    /// one module type path unify their type arguments by name. O(arguments
    /// log arguments). (R3g)
    pub fn unify_package(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `reify` (compiler/ml/ctype.ml:1813-1870): replace the variables of a
    /// type by fresh abstract types at the newtype level, in pattern mode.
    /// O(nodes), marks. (R3h)
    pub fn reify(&mut self, ty: Ty) {
        todo!("R3h")
    }

    /// `add_gadt_equation` (compiler/ml/ctype.ml:2093-2100): give the
    /// locally abstract type `source` the manifest `destination` when the
    /// equation is well-founded, and clean the memos. O(nodes of
    /// `destination`). (R3h)
    pub fn add_gadt_equation(&mut self, source: u32, destination: Ty) {
        todo!("R3h")
    }

    /// `mcomp` (compiler/ml/ctype.ml:1905-2090): whether two types can have
    /// a common instance; never links. O(pairs), pair set, explicit stack.
    /// (R3h)
    pub fn mcomp(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3h")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<FieldRef>(), 12);
    }
}
