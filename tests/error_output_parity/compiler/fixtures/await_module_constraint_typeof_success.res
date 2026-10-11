// error-output-parity: bs_builtin_ppx leaves constrained module-type-of await aliases valid.
module M = await (Belt.List: module type of Belt.List)
