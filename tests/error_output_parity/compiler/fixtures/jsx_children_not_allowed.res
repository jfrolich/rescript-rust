// error-output-parity: Typecore.Wrong_name JSX children prop branch
module React = {
  type element = Jsx.element
  type componentLike<'props, 'return> = Jsx.componentLike<'props, 'return>
  type component<'props> = Jsx.component<'props>
  external component: componentLike<'props, element> => component<'props> = "%identity"
  @module("react/jsx-runtime")
  external jsx: (component<'props>, 'props) => element = "jsx"
  @val external null: element = "null"
}

module Button = {
  @react.component
  let make = () => React.null
}

let element = <Button> {React.null} </Button>
