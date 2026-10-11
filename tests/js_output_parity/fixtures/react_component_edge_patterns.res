module React = {
  type element = Jsx.element
  type componentLike<'props, 'return> = Jsx.componentLike<'props, 'return>
  type component<'props> = Jsx.component<'props>
  type ref<'a>

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
  external jsxsKeyed: (
    component<'props>,
    'props,
    ~key: string=?,
    @ignore unit,
  ) => element = "jsxs"
  type fragmentProps = {children?: element}
  @module("react/jsx-runtime") external jsxFragment: component<fragmentProps> = "Fragment"

  @module("react") external memo: component<'props> => component<'props> = "memo"
  @module("react")
  external forwardRef: (('props, Nullable.t<ref<'a>>) => element) => component<'props> =
    "forwardRef"
  @module("react") external cloneElement: (element, 'props) => element = "cloneElement"
  @module("react") external useState: (unit => 'state) => ('state, 'state => unit) = "useState"
  @module("react")
  external useEffect2: (unit => option<unit => unit>, ('a, 'b)) => unit = "useEffect"
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

module AliasedDefaults = {
  @react.component
  let make = (~count=1, ~double=count * 2, ~label as text="count") =>
    <span title={text}> {React.int(count + double)} </span>
}

module ModuleProp = {
  module type Display = {
    let value: int
    @react.component
    let make: unit => React.element
  }

  @react.component
  let make = (~display as module(Display: Display), ~pair as (left, right), ~children=?) =>
    <section>
      <Display />
      {React.int(Display.value + left + right)}
      {children->Option.getOr(React.null)}
    </section>
}

module DisplayImpl = {
  let value = 7

  @react.component
  let make = () => <strong> {React.string("display")} </strong>
}

module Forwarded = {
  @react.component
  let make = React.forwardRef((~className=?, ~children, _ref) => {
    let _: option<string> = className
    children
  })
}

module Hooked = {
  @react.component
  let make = (~initial, ~label, ~child=?) => {
    let (count, setCount) = React.useState(() => initial)
    React.useEffect2(() => {
      setCount(count + 1)
      None
    }, (count, label))

    let baseChild = child->Option.getOr(<span> {React.string(label)} </span>)
    React.cloneElement(baseChild, {"dataCount": count})
  }
}

module MemoedHooked = {
  @react.component
  let make = (~initial, ~label) => <Hooked initial label />
  let make = React.memo(make)
}

let aliasedDefault = <AliasedDefaults label="ready" count=3 />
let modulePropJsx =
  <ModuleProp display=module(DisplayImpl) pair={(1, 5)}>
    <AliasedDefaults />
  </ModuleProp>
let forwarded = <Forwarded className="frame"> {React.string("child")} </Forwarded>
let hooked = <Hooked initial=2 label="tap" child={<span title="child" />} />
let memoed = <MemoedHooked initial=5 label="memo" />

let allValues = (
  aliasedDefault,
  modulePropJsx,
  forwarded,
  hooked,
  memoed,
)
