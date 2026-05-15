@@uncurried

type dateFormatOptions = {someOption?: bool}

@module("SomeModule")
external formatDate: (Js.Date.t, ~options: dateFormatOptions=?, ~done: bool=?) => string =
  "formatDate"

@send external floatToString: (float, ~radix: int=?) => string = "toString"

@new external regExpFromString: (string, ~flags: string=?) => Js.Re.t = "RegExp"

let dateValue = Js.Date.make()

let formatValues = (
  formatDate(dateValue),
  formatDate(dateValue, ~options={someOption: true}),
  formatDate(dateValue, ~done=true),
  formatDate(dateValue, ~options={someOption: false}, ~done=false),
)

let numberStringValues = (floatToString(42.), floatToString(42., ~radix=16))

let regexpValues = (
  regExpFromString("ab+c"),
  regExpFromString("ab+c", ~flags="i"),
)
