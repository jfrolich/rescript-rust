// error-output-parity: Typemod.With_no_component
module type S = {}

module type T = S with type missing = int
