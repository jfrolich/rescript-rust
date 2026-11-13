module ReactDOM = {
  @instanceOf("Element") type element
}

module WebAPI = {
  @instanceOf("Element")
  type element = private {tagName: string, mutable id: string}
}

// Neither branch is the expected type of the other, so the compiler does
// not choose: write the coercion on one of them.
//   useOwn ? mine : (theirs :> ReactDOM.element)
let pick = (useOwn, mine: ReactDOM.element, theirs: WebAPI.element) =>
  useOwn ? mine : theirs
