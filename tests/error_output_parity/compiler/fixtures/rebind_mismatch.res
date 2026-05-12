// error-output-parity: Typedecl.Rebind_mismatch
type t = ..
type u = t
type t += A
type u += B = A
