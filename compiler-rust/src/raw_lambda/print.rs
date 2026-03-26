//! Raw Lambda printer.

use std::fmt;

use crate::raw_lambda::RawLambda;

/// Pretty-printer for raw lambda.
pub struct RawLambdaPrinter<'a> {
    raw: &'a RawLambda,
}

impl<'a> RawLambdaPrinter<'a> {
    /// Create a new raw-lambda printer.
    pub fn new(raw: &'a RawLambda) -> Self {
        Self { raw }
    }
}

impl fmt::Display for RawLambdaPrinter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lowered = self.raw.clone().into_lowered();
        write!(f, "{}", crate::lambda::print::RawLambdaPrinter::new(&lowered))
    }
}
