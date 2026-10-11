// error-output-parity: JSX component signatures reject duplicate prop names.
@react.component
let make: (~x: int, ~x: string) => React.element
