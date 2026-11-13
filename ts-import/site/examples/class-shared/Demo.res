// Two packages, each with its own declaration of the class Element.
module ReactDOM = {
  @instanceOf("Element") type element
  type root
  external createRoot: element => root = "createRoot"
  @val external querySelector: string => Null.t<element> = "document.querySelector"
}

module WebAPI = {
  @instanceOf("Element")
  type element = private {tagName: string, mutable id: string}
  @send external focus: element => unit = "focus"
}

// Both types say "an instance of Element", so a value of one is accepted
// where the other is expected.
let mount = (container: WebAPI.element) => ReactDOM.createRoot(container)

let focus = (el: ReactDOM.element) => WebAPI.focus(el)
