open Macro

let capitalize = (text: string) =>
  String.toUpperCase(String.charAt(text, 0)) ++ String.slice(text, ~start=1)

// A macro can return any number of declarations: here two conversion
// functions per unit. Used as `module Length = %Units.table(...)`.
@macro
let table = (base: string, units: array<(string, float)>): decls =>
  Code.decls(
    units->Array.map(((unit, factor)) =>
      %code(
        let ${Pat.var(unit ++ "To" ++ capitalize(base))} = (value: float) => value *. ${Code.float(factor)}
        let ${Pat.var(base ++ "To" ++ capitalize(unit))} = (value: float) => value /. ${Code.float(factor)}
      )
    ),
  )
