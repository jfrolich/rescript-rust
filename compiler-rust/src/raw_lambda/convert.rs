//! Typedtree -> Raw Lambda scaffolding.
//!
//! The raw stage is split from the lowered Lambda stage so `-drawlambda`
//! can be aligned with OCaml independently from JS code generation.

use crate::lambda::convert::LambdaConverter;
use crate::parse_arena::ParseArena;
use crate::raw_lambda::RawLambda;
use crate::types::typedtree::Structure;

/// Converter from typedtree to raw lambda.
pub struct RawLambdaConverter<'a> {
    lowered: LambdaConverter<'a>,
}

impl<'a> RawLambdaConverter<'a> {
    /// Create a new raw-lambda converter.
    pub fn new(arena: &'a ParseArena) -> Self {
        Self {
            lowered: LambdaConverter::new(arena),
        }
    }

    /// Convert a structure into raw lambda.
    pub fn convert_structure(&mut self, structure: &Structure) -> RawLambda {
        RawLambda::from_lowered(self.lowered.convert_structure(structure))
    }
}
