open Macro

// A value for every type, chosen by the type the call site expects.
@generic
let value = (_: code<unit>): code<'a> =>
  switch Type.info(expected()) {
  | Int => %code(0)
  | Float => %code(0.0)
  | String => %code("")
  | Bool => %code(false)
  | Array(_) => %code([])
  | Option(_) => %code(None)
  | Record({fields}) => Code.record(fields->Array.map(f => (f.name, %code(value()))))
  | Variant({constructors}) =>
    switch constructors->Array.find(c => c.args->Array.length == 0 && c.fields->Array.length == 0) {
    | Some(c) => Code.ident(c.name)
    | None => error(`Default.value: ${Type.name(expected())} has no constructor without arguments`)
    }
  | _ => error(`Default.value: there is no default for ${Type.name(expected())}`)
  }
