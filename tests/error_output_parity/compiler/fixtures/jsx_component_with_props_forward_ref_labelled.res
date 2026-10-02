// check_invalid_forward_ref inspects all parameters of the forwardRef function.
@react.componentWithProps
let make = React.forwardRef(( _ref,~value) => value)
