open Macro

// A macro attached to a type receives the checked declaration and returns
// declarations, which are added after the type.
@macro
let derive = (t: Type.decl): decls =>
  switch Type.info(t.typ) {
  | Variant({constructors}) =>
    constructors->Array.forEach(c =>
      if c.args->Array.length > 0 || c.fields->Array.length > 0 {
        error(`Enum.derive: the constructor ${c.name} has arguments`)
      }
    )
    let label = (c: Type.constructor) => c.attrs->Attr.string("Enum.label")->Option.getOr(c.jsName)
    let value = (c: Type.constructor): code<unknown> => Code.ident(c.name)

    let toString = Code.switch_(
      %code(value),
      constructors->Array.map(c => {
        let (pattern, _) = Pat.constructor(c)
        (pattern, Code.string(label(c)))
      }),
    )
    let known = constructors->Array.map(c => (Pat.string(label(c)), %code(Some(${value(c)}))))
    let fromString = Code.switch_(%code(text), [...known, (Pat.any, %code(None))])

    %code(
      let ${Pat.var(t.name ++ "ToString")} = (value: ${t.typ}): string => ${toString}
      let ${Pat.var(t.name ++ "FromString")} = (text: string): option<${t.typ}> => ${fromString}
      let ${Pat.var(t.name ++ "Values")}: array<${t.typ}> = ${Code.array(constructors->Array.map(value))}
    )
  | _ => error("Enum.derive needs a variant type")
  }
