@@uncurried

type binary = (int, int) => int

@val external implicitArity: binary = "outputParityImplicitArity"
@val external explicitArity: (int, int) => int = "outputParityExplicitArity"

let directValues = (
  implicitArity(1, 2),
  explicitArity(3, 4),
)

module FromTypeConstructor = {
  type fn<'props, 'return> = 'props => 'return

  external aliasArity: fn<int, int> = "outputParityAliasArity"
  external directArity: int => int = "outputParityDirectArity"
  external optionalArity: (~x: int=?, ~y: int) => int = "outputParityOptionalArity"

  let values = (
    aliasArity(10),
    directArity(20),
    optionalArity(~y=3),
    optionalArity(~x=2, ~y=3),
  )
}

module React = {
  type element = Jsx.element
  type componentLike<'props, 'return> = 'props => 'return
  type component<'props> = Jsx.component<'props>

  external string: string => element = "%identity"

  @module("react/jsx-runtime")
  external jsx: (component<'props>, 'props) => element = "jsx"
}

module FormattedMessage = {
  @react.component @module("react-intl")
  external make: (~id: string, ~defaultMessage: string) => React.element =
    "FormattedMessage"
}

let jsxValue = <FormattedMessage id="test" defaultMessage="Test" />
