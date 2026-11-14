@instanceOf("Error")
type t

@pure @get external stack: t => option<string> = "stack"
@pure @get external message: t => string = "message"
@pure @get external name: t => string = "name"
@pure @get external fileName: t => option<string> = "fileName"

@pure @new external make: string => t = "Error"

@pure
external throw: t => 'a = "%raise"

let throwWithMessage = str => {
  let error = make(str)
  throw(error)
}

module EvalError = {
  @pure @new external make: string => t = "EvalError"
  let throwWithMessage = s => make(s)->throw
}

module RangeError = {
  @pure @new external make: string => t = "RangeError"
  let throwWithMessage = s => make(s)->throw
}

module ReferenceError = {
  @pure @new external make: string => t = "ReferenceError"
  let throwWithMessage = s => make(s)->throw
}

module SyntaxError = {
  @pure @new external make: string => t = "SyntaxError"
  let throwWithMessage = s => make(s)->throw
}

module TypeError = {
  @pure @new external make: string => t = "TypeError"
  let throwWithMessage = s => make(s)->throw
}

module URIError = {
  @pure @new external make: string => t = "URIError"
  let throwWithMessage = s => make(s)->throw
}

let panic = msg => make(`Panic! ${msg}`)->throw

@pure
external toJsExn: t => Stdlib_JsExn.t = "%identity"

@pure
external ignore: t => unit = "%ignore"
