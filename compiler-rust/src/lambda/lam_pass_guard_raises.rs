//! Port of `compiler/core/lam_pass_guard_raises.ml`.
//!
//! `if a then raise e else c` becomes `(if a then raise e else ()); c`, so the
//! continuation is not nested inside a branch. This is code motion rather
//! than normalization, so it runs as the last Lambda pass instead of inside
//! [`Lambda::if_`]: matching inspects the terms it builds, and rewriting them
//! during construction would leave static raises without their catch.

use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lambda_traverse::{Mapped, shallow_map_sharing};
use crate::lambda::{Lambda, PrimInfo};

/// `Lam_pass_guard_raises.guard_raises`.
pub fn guard_raises(lam: Lambda) -> Lambda {
    guard_raises_mapped(lam).0
}

fn guard_raises_mapped(lam: Lambda) -> Mapped {
    match lam {
        Lambda::LifThenElse(a, b, c)
            if matches!(
                b.as_ref(),
                Lambda::Lprim(prim) if matches!(prim.as_ref(), PrimInfo { primitive: Primitive::Praise, .. })
            ) && !matches!(c.as_ref(), Lambda::Lconst(_)) =>
        {
            let (a, _) = guard_raises_mapped(*a);
            let (c, _) = guard_raises_mapped(*c);
            (Lambda::seq(Lambda::if_(a, *b, Lambda::unit()), c), true)
        }
        // A constant alternative is already as flat as it gets.
        lam => shallow_map_sharing(lam, &mut guard_raises_mapped),
    }
}
