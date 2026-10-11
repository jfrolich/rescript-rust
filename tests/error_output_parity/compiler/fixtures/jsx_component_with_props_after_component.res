// error-output-parity: @react.componentWithProps does not participate in @react.component multiplicity.
@react.component
let make = () => React.null

type props = {value: int}

@react.componentWithProps
let make2 = (props: props) => React.null
