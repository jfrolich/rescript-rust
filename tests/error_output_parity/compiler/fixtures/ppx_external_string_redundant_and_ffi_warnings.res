external f: @string [#a | #b] => unit = "f"
external g: (@string [#a | #b], ~x: int=?) => @variadic unit = "g"
let x = %ffi("(a) => {")
let y = %ffi("1 +")
