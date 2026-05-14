// error-output-parity: Typetexp.Unbound_constructor for a qualified Pext_rebind target.
type t = ..

module M = {}

type t += B = M.Missing
