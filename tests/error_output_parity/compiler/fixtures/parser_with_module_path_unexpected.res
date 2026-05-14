// error-output-parity: with-module constraints require uppercase module paths.
module type S = {}
module type T = S with module foo = Bar
