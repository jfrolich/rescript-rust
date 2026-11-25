module ReactDOM = {
  @instanceOf("Node") type node
  @instanceOf("Element") type element = private node
}

module WebAPI = {
  @instanceOf("Element")
  type element = private {tagName: string, mutable id: string}
  @send external focus: element => unit = "focus"
}

// A variant with a case for each package's type.
@unboxed type bridge = Theirs(WebAPI.element) | Mine(ReactDOM.node)

// Wrap React's element in its own case, match it in the other one.
let focus = (el: ReactDOM.element) =>
  switch Mine((el :> ReactDOM.node)) {
  | Theirs(el) => WebAPI.focus(el)
  | Mine(_) => ()
  }
