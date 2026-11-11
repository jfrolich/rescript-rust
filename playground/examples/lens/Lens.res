open Macro

type t<'record, 'field> = {
  get: 'record => 'field,
  set: ('record, 'field) => 'record,
}

let update = (record, lens, f) => lens.set(record, f(lens.get(record)))

@macro
let derive = (t: Type.decl): decls =>
  switch Type.info(t.typ) {
  | Record({fields}) =>
    Code.decls(
      fields->Array.map(f => {
        let name = t.name ++ "_" ++ f.name
        %code(
          let ${Pat.var(name)}: Lens.t<${t.typ}, ${f.typ}> = {
            get: record => ${Code.field(%code(record), f.name)},
            set: (record, value) => ${Code.raw(`{...record, ${f.name}: value}`)},
          }
        )
      }),
    )
  | _ => error("Lens.derive needs a record type")
  }
