// error-output-parity: Bs_ast_invariant warns for unused @string on value argument annotations.
let f = (~_kind: @string [#a]) => 1
