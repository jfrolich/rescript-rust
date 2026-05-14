// error-output-parity: JSX v4 rejects multiple @react.component signatures in one module.
@react.component
let make: unit => React.element

@react.component
let make2: unit => React.element
