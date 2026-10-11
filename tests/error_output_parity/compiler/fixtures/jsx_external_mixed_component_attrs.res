// error-output-parity: JSX externals reject mixing component and componentWithProps.
@react.component
@react.componentWithProps
external make: unit => React.element = "make"
