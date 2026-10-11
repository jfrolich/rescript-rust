// error-output-parity: Typetexp.Unbound_module from qualified module type of
module M = {}
module type T = module type of M.Missing
