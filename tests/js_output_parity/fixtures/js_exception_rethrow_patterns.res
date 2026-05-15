exception Wrapped(string)

let parseOrTag = source =>
  switch JSON.parseOrThrow(source) {
  | exception JsExn(error) =>
    JsExn.ignore(error)
    #JsException
  | JSON.String(value) => #String(value)
  | _ => #OtherJson
  }

let catchJsValue = value =>
  try {
    JsExn.throw(value)
  } catch {
  | JsExn(error) as caught =>
    let wrapped = JsExn.fromException(caught)
    switch (JsExn.message(error), wrapped) {
    | (Some(message), Some(_)) => message
    | (None, Some(_)) => "js"
    | _ => "unknown"
    }
  | exn => throw(exn)
  }

let rethrowKnown = run =>
  try {
    try {
      run()
    } catch {
    | Wrapped(value) as exn =>
      if String.length(value) > 3 {
        throw(exn)
      } else {
        value
      }
    | exn => throw(exn)
    }
  } catch {
  | Wrapped(value) => value ++ "!"
  | JsExn(error) =>
    JsExn.ignore(error)
    "js!"
  | _ => "other!"
  }

let switchExceptionResult = run =>
  switch run() {
  | exception JsExn(error) =>
    JsExn.ignore(error)
    "js-switch"
  | exception Wrapped(value) => value
  | value => value
  }

let allValues = (
  parseOrTag(`"ok"`),
  parseOrTag(`{"unterminated"`),
  catchJsValue(%raw(`new Error("boom")`)),
  rethrowKnown(() => throw(Wrapped("long"))),
  rethrowKnown(() => throw(Wrapped("ok"))),
  switchExceptionResult(() => JsExn.throw("plain")),
  switchExceptionResult(() => "done"),
)
