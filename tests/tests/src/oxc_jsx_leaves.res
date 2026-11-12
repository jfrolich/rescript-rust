@@config({flags: ["-bs-jsx", "4", "-bs-jsx-preserve"]})

module Widget = {
  @react.component @module("example-ui")
  external make: (~label: string) => React.element = "Widget"
}

let intrinsic = label => <input title=label />
let component = label => <Widget label />
let spread = (props: JsxDOM.domProps, label) => <input {...props} title=label key="sample" />
let emptyFragment = <></>
