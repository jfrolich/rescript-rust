module React = {
  type element = Jsx.element

  external string: string => element = "%identity"
  external array: array<element> => element = "%identity"
}

module ReactDOM = {
  type domProps = JsxDOM.domProps

  external someElement: React.element => option<React.element> = "%identity"

  @module("react/jsx-runtime") external jsx: (string, domProps) => Jsx.element = "jsx"
  @module("react/jsx-runtime") external jsxs: (string, domProps) => Jsx.element = "jsxs"
  @module("react/jsx-runtime")
  external jsxKeyed: (
    string,
    domProps,
    ~key: string=?,
    @ignore unit,
  ) => Jsx.element = "jsx"
  @module("react/jsx-runtime")
  external jsxsKeyed: (
    string,
    domProps,
    ~key: string=?,
    @ignore unit,
  ) => Jsx.element = "jsxs"
}

let single = <div title="root" />

let nested =
  <section dataTestId="container">
    <h1> {React.string("Title")} </h1>
    <button disabled=true> {React.string("Save")} </button>
  </section>

let spreadProps: JsxDOM.domProps = {
  title: "spread",
  className: "primary",
}

let withSpread =
  <div {...spreadProps} title="override">
    {React.string("Body")}
  </div>
