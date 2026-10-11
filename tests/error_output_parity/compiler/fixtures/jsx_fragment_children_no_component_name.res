// Error_message_utils.path_to_jsx_component_name only names `...Component.props`;
// a fragment has no component name.
@@config({
  flags: ["-bs-jsx", "4"],
})

module React = {
  type element = Jsx.element
  type componentLike<'props, 'return> = 'props => 'return
  type component<'props> = Jsx.component<'props>
  external component: componentLike<'props element> => component<'b> = "%component_identity"

  @module("react/jsx-runtime")
  external jsx: (component<'props>, 'props) => element = "jsx"

  type fragmentProps = {}
  @module("react/jsx-runtime") external jsxFragment: component<fragmentProps> = "Fragment"
}

let x = <> {""} </>
