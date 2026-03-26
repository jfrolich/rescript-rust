//! Raw Lambda -> lowered Lambda boundary.

use crate::lambda::Lambda;
use crate::raw_lambda::RawLambda;

/// Lower raw lambda into the existing JS-facing Lambda IR.
pub fn lower_to_lambda(raw: RawLambda) -> Lambda {
    raw.into_lowered()
}
