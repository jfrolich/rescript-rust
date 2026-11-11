open Macro

// Macro.readFile reads a file of the project while compiling. The build
// knows the macro depends on it.
let messages = () =>
  switch JSON.parseOrThrow(readFile("en.json")) {
  | Object(messages) => messages
  | _ => error("en.json has to be an object")
  }

// "Hello {name}" as ["Hello ", "name", ""]: text and placeholders in turn.
let pieces = (text: string) => text->String.splitByRegExp(/[{}]/)->Array.map(piece => piece->Option.getOr(""))

@macro
let t = (key: string): code<'a> =>
  switch messages()->Dict.get(key) {
  | Some(String(text)) =>
    let pieces = pieces(text)
    let names = pieces->Array.filterWithIndex((_, i) => mod(i, 2) == 1)
    let parts =
      pieces->Array.mapWithIndex((piece, i) => mod(i, 2) == 1 ? Code.ident(piece) : Code.string(piece))
    let body = parts->Array.reduce(%code(""), (text, part) => %code(${text} ++ ${part}))
    // A message without placeholders is a string, one with placeholders a
    // function with a labelled argument for each.
    names->Array.length == 0
      ? Code.string(text)
      : Code.fn(names->Array.map(name => Code.labelled(name, %type(string))), body)
  | _ =>
    let known = messages()->Dict.keysToArray->Array.join(", ")
    error(`There is no message "${key}" in en.json. It has: ${known}`)
  }
