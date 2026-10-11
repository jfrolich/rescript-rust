// error-output-parity: JSX v4 rejects duplicate @react.component attributes on externals.
@react.component
@react.component
external make: unit => React.element = "make"
