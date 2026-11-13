// Two packages, each with its own declaration of the class Element.
module ReactDOM = {
  @instanceOf("Element") type element
  @val external querySelector: string => Null.t<element> = "document.querySelector"
}

module WebAPI = {
  @instanceOf("Element")
  type element = private {tagName: string, mutable id: string}
  @send external focus: element => unit = "focus"
}

// Both types say "an instance of Element". They are still two types.
let focus = (el: ReactDOM.element) => WebAPI.focus(el)
