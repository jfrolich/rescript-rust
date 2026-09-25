// Generated fragment nodes use Location.none, so the header shows the input file name.
@@config({
  flags: ["-bs-jsx", "4"],
})

module React = {
  type element = Jsx.element
  type componentLike<'props, 'return> = 'props => 'return
  type component<'props> = Jsx.component<'props>
  external component: componentLike<'props, element> => component<'props> = "%component_identity"

  @module("react/jsx-runtime")
  external jsxFragment: (component<'props>, 'props) => element = "jsx"

  type fragmentProps = {children?: element}
  @module("react/jsx-runtime") external jsxFragment: component<fragmentProps> = "Fragment"
}

let x = <> {None} </>
