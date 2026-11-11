type props = {a: int}
@react.componentWithProps(x)
let make = (props: props) => props.a
