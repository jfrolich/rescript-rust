// error-output-parity: map_binding checks for a second component before get_fn_name rejects the pattern.
@react.component
let make = () => React.null

@react.component
let ...make2 = () => React.null
