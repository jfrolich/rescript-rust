module Forms = {
  @instanceOf("Element") type element
  @instanceOf("HTMLInputElement") type input = private element
}

module WebAPI = {
  @instanceOf("Element") type element = private {tagName: string}
}

// The cases come from two packages. `Forms.input` says its class has
// Element as an ancestor, so it is tested first.
@unboxed type target = Element(WebAPI.element) | Input(Forms.input)

let describe = (target: target) =>
  switch target {
  | Element(el) => el.tagName
  | Input(_) => "input"
  }
