module ReactDOM = {
  @instanceOf("Node") type node
  @instanceOf("Element") type element = private node
  type root
  external createRoot: element => root = "createRoot"
}

module Forms = {
  // Nothing here says that an HTMLInputElement is an Element. Declare the
  // chain and the last line compiles:
  //   @instanceOf("Element") type element
  //   @instanceOf("HTMLInputElement") type input = private element
  @instanceOf("HTMLInputElement") type input
}

let mount = (input: Forms.input) => ReactDOM.createRoot((input :> ReactDOM.element))
