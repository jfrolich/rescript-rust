module React = {
  type element = Jsx.element
  type componentLike<'props, 'return> = Jsx.componentLike<'props, 'return>
  type component<'props> = Jsx.component<'props>

  external component: componentLike<'props, element> => component<'props> = "%component_identity"
  let null: element = %raw("null")
  external string: string => element = "%identity"
  external int: int => element = "%identity"
  external array: array<element> => element = "%identity"
  @module("react/jsx-runtime") external jsx: (component<'props>, 'props) => element = "jsx"
  @module("react/jsx-runtime")
  external jsxKeyed: (component<'props>, 'props, ~key: string=?, @ignore unit) => element = "jsx"
  @module("react/jsx-runtime") external jsxs: (component<'props>, 'props) => element = "jsxs"
  @module("react/jsx-runtime")
  external jsxsKeyed: (component<'props>, 'props, ~key: string=?, @ignore unit) => element = "jsxs"
  type fragmentProps = {children?: element}
  @module("react/jsx-runtime") external jsxFragment: component<fragmentProps> = "Fragment"
  @module("react") external memo: component<'props> => component<'props> = "memo"
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

module Icon = {
  @react.component
  let make = (~title: string=?) =>
    <span className="icon"> {React.string(title->Option.getOr("icon"))} </span>
}

module Button = {
  @react.component
  let make = (~label: string, ~disabled=false, ~children=?) =>
    <button disabled={disabled} dataTestId="action">
      {React.string(label)}
      {children->Option.getOr(React.null)}
    </button>
}

module WeirdProps = {
  type props = {\"MyWeirdProp": string}

  @react.componentWithProps
  let make = props => <p> {React.string(props.\"MyWeirdProp")} </p>
}

let spreadProps: JsxDOM.domProps = {
  title: "spread",
  className: "primary",
}

let single = <div title="root" />

let nested =
  <section dataTestId="container">
    <h1> {React.string("Title")} </h1>
    <Button label="Save" disabled=true>
      <Icon title="disk" />
    </Button>
  </section>

let withSpread =
  <div {...spreadProps} title="override" key="spread-key">
    {React.string("Body")}
  </div>

let escapedProp = <WeirdProps \"MyWeirdProp"="value" />

let fragment = <>
  <Icon />
  {React.int(3)}
</>

module Memoed = {
  @react.component
  let make = () => <Icon title="memoed" />
  let make = React.memo(make)
}

let memoElement = <Memoed />

let allValues = (
  single,
  nested,
  withSpread,
  escapedProp,
  fragment,
  memoElement,
)
