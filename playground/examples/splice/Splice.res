open Macro

// `${...items}` is a splice hole: it stands for any number of items of a
// list in a quote. The rest of the quote stays ordinary code.

// Fields of a record, after fields the quote writes itself.
// `rest` is an array of entries, as Code.record takes.
@generic
let withKey = (value: code<'a>, key: code<string>): code<'b> =>
  switch Type.info(typeOf(value)) {
  | Record({fields}) =>
    let rest = fields->Array.map(f => Code.entryOf(f, value->Code.field(f.name)))
    %code({key: ${key}, version: 1, ${...rest}})
  | _ => error("Splice.withKey needs a record")
  }

// Arguments of a call: an array of code.
@generic
let call = (f: code<'f>, value: code<'a>): code<'b> =>
  switch Type.info(typeOf(value)) {
  | Record({fields}) =>
    let args = fields->Array.map(f => value->Code.field(f.name))
    %code(${f}(${...args}))
  | _ => error("Splice.call needs a record")
  }

// Cases of a switch, before a case of the quote: an array of a pattern and
// the code of its case.
@generic
let parse = (text: code<string>): code<'a> =>
  switch Type.info(expected()) {
  | Option(inner) =>
    switch Type.info(inner) {
    | Variant({constructors}) =>
      let cases = constructors->Array.map(c => (
        Pat.string(String.toLowerCase(c.name)),
        %code(Some(${Code.ident(c.name)})),
      ))
      %code(
        switch String.toLowerCase(${text}) {
        ${...cases}
        | _ => None
        }
      )
    | _ => error("Splice.parse needs a variant")
    }
  | _ => error("Splice.parse returns an option")
  }
