// error-output-parity: JSX component externals reject duplicate prop names.
@react.component
external make: (~x: int, ~x: string) => React.element = "make"
