// Bs_builtin_ppx.structure_mapper maps later items first, so the error of
// the second duplicate is reported.
@deriving({abstract: unknown}) type t = {x: int}
@deriving({abstract: unknown}) type u = {x: int}
