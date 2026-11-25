module ReactDOM = {
  @instanceOf("Node") type node
  @instanceOf("Element") type element = private node
}

module WebAPI = {
  @instanceOf("Node")
  type node = private {nodeName: string}

  @instanceOf("Element") @extends(: node)
  type element = private {nodeName: string, tagName: string, mutable id: string}

  @instanceOf("HTMLInputElement") @extends(: element)
  type input = private {nodeName: string, tagName: string, mutable id: string, mutable value: string}
}

// The same class, in both directions.
let tag = (el: ReactDOM.element) => (el :> WebAPI.element).tagName
let back = (el: WebAPI.element) => (el :> ReactDOM.element)

// A subclass, to another package's declaration of an ancestor.
let node = (input: WebAPI.input) => (input :> ReactDOM.node)

// Inside other types the coercion follows variance.
let maybe = (input: option<WebAPI.input>) => (input :> option<ReactDOM.element>)
let listener = (f: ReactDOM.node => unit) => (f :> WebAPI.input => unit)

// A ref is read and written, so its content must be equal on both sides.
// Two declarations of one class are.
type ref<'a> = {mutable current: 'a}
let ref = (ref: ref<Null.t<ReactDOM.element>>) => (ref :> ref<Null.t<WebAPI.element>>)
