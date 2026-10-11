// error-output-parity: Bs_ast_invariant warns for every unused built-in ReScript attribute name.
let asAttr = (~_x: @as("x") int) => 1
let configAttr = (~_x: @config int) => 1
let ignoreAttr = (~_x: @ignore int) => 1
let intAttr = (~_x: @int [#a]) => 1
let optionalAttr = (~_x: @optional int) => 1
let unwrapAttr = (~_x: @unwrap [#A(int)]) => 1
