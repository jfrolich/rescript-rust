// error-output-parity: Typemod.Structure_expected
module type S = {}

module F = (X: S) => {}

open F
