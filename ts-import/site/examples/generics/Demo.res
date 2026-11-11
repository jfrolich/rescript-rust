let {parseNumber, first, mapPage} = %ts("./result.ts")

// `Result<number>`: the default for `E` is filled in by TypeScript.
let double = text =>
  switch parseNumber(text) {
  | Ok({value}) => Some(value *. 2.)
  | NotOk({error}) =>
    Console.error(error)
    None
  }

// Type parameters are type variables: `page<'t>`, `first: page<'t> => option<'t>`.
let page = {items: ["a", "b", "c"]}
let lengths = mapPage(page, (item, _index) => String.length(item))
let firstLength = first(lengths)
