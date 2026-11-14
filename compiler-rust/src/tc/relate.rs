//! R3 skeleton: the relations that do not unify for good: `moregeneral`,
//! `equal`, `matches` (slice R3i) and subtyping (slice R3j). See
//! CHECKER_REWRITE.md, "R3 as designed".

use super::graph::Ty;
use super::unify::{Checker, Clash};

/// One delayed constraint of subtyping (`cstrs`,
/// compiler/ml/ctype.ml:3647): 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Constraint {
    pub left: Ty,
    pub right: Ty,
    /// Length of the trace when the constraint was made, `Mode::Explain`.
    pub trace: u32,
}

impl Checker {
    /// `moregeneral` (compiler/ml/ctype.ml:3104-3148): whether `pattern` is
    /// at least as general as `subject`, both schemes. One instance of each,
    /// one `moregen` walk (ctype.ml:2925) under a speculation that is always
    /// restored. O(nodes of both schemes). (R3i)
    pub fn moregeneral(&mut self, inst_nongen: bool, pattern: Ty, subject: Ty) -> bool {
        todo!("R3i")
    }

    /// `equal` (compiler/ml/ctype.ml:3372-3380): structural equality of two
    /// lists of types, up to a renaming of variables when `rename`
    /// (`eqtype`, ctype.ml:3200). Never links. O(pairs), pair set, explicit
    /// stack. (R3i)
    pub fn equal(&mut self, rename: bool, left: &[Ty], right: &[Ty]) -> bool {
        todo!("R3i")
    }

    /// `matches` (compiler/ml/ctype.ml:3167-3182): whether `ty` unifies
    /// with `pattern` without instantiating a variable of `ty`
    /// (`rigidify`, ctype.ml:3150). One unification under a speculation that
    /// is always restored, and a memo cleanup. (R3i)
    pub fn matches(&mut self, ty: Ty, pattern: Ty) -> bool {
        todo!("R3i")
    }

    /// `subtype` (compiler/ml/ctype.ml:4216-4225) without the checks that
    /// read a declaration's labels or constructors (those belong to R6e,
    /// see "R3 as designed", decision 6): collect the constraints of
    /// `left :> right` into `out` (`subtype_rec`, ctype.ml:3647). O(pairs),
    /// pair set, explicit stack. (R3j)
    pub fn subtype(&mut self, left: Ty, right: Ty, out: &mut Vec<Constraint>) -> Result<(), Clash> {
        todo!("R3j")
    }

    /// Unify the delayed constraints, in order (the closure `subtype`
    /// returns, compiler/ml/ctype.ml:4221-4225). O(constraints) plus the
    /// unifications. (R3j)
    pub fn force_subtype(&mut self, constraints: &[Constraint]) -> Result<(), Clash> {
        todo!("R3j")
    }

    /// `enlarge_type` (compiler/ml/ctype.ml:3593-3613): the supertype a
    /// coercion without a source annotation goes to, and whether it is the
    /// type itself (`build_subtype`, ctype.ml:3431). O(nodes), marks. (R3j)
    pub fn enlarge_type(&mut self, ty: Ty) -> (Ty, bool) {
        todo!("R3j")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Constraint>(), 12);
    }
}
