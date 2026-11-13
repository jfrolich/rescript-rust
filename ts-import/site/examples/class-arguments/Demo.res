module ReactDOM = {
  @instanceOf("Node") type node
  @instanceOf("Element") type element = private node
  type root
  external createRoot: element => root = "createRoot"
  external observe: (~target: node, ~root: element=?) => unit = "observe"
  type ref<'a> = {mutable current: 'a}
  external useRef: unit => ref<Null.t<element>> = "useRef"
}

module WebAPI = {
  @instanceOf("Node")
  type node = private {nodeName: string}

  @instanceOf("Element") @extends(: node)
  type element = private {nodeName: string, tagName: string, mutable id: string}

  @instanceOf("HTMLInputElement") @extends(: element)
  type input = private {nodeName: string, tagName: string, mutable id: string, mutable value: string}

  @send external focus: element => unit = "focus"
  external measure: ReactDOM.ref<Null.t<element>> => float = "measure"
}

type portal = {container: ReactDOM.element, title: string}
type target = Element(ReactDOM.element) | Window

// An argument: the same class, or a subclass.
let mount = (input: WebAPI.input) => ReactDOM.createRoot(input)
let focus = (el: ReactDOM.element) => el->WebAPI.focus

// A labelled and an optional argument.
let observe = (input: WebAPI.input, el: WebAPI.element) =>
  ReactDOM.observe(~target=input, ~root=el)

// The same class inside the type of the argument.
let width = () => WebAPI.measure(ReactDOM.useRef())

// A field of a record and the payload of a constructor.
let portal = (input: WebAPI.input) => {container: input, title: "Settings"}
let target = (el: WebAPI.element) => Element(el)
