open Macro

// A macro is a function the compiler runs while it compiles another file.
// `e` is the code of the argument, not its value. The quote %code(...) is
// the code the macro returns; ${...} is a hole in it.
@macro
let log = (e: code<'a>): code<'a> =>
  %code({
    let value = ${e}
    Console.log2(${Code.string(Code.print(e) ++ " =")}, value)
    value
  })

@macro
let check = (condition: code<bool>): code<unit> =>
  %code(
    if !${condition} {
      Console.error(${Code.string("Check failed: " ++ Code.print(condition))})
    }
  )
