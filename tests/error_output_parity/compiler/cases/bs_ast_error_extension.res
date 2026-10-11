// Depend.handle_extension raises on [%error] while writing the binary AST.
let x = 1
%%error("dependency extraction reaches this error")
let y = x
