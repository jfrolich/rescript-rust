// error-output-parity: Typetexp.Unbound_modtype qualified module type
module M = {}

module type T = M.Missing
