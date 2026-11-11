open Macro

let wrap = (name: string, f: 'a => 'b): ('a => 'b) =>
  argument => {
    Console.log2("call", name)
    f(argument)
  }

// A macro attached to a let receives the binding before it is type
// checked, and returns what replaces it.
@macro
let calls = (binding: Decl.value): decls =>
  %code(let ${binding.pat} = Trace.wrap(${Code.string(binding.name)}, ${binding.expr}))
