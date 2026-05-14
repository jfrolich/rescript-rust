// error-output-parity: JSX v4 emits Warnings.Preprocessor for optional prop annotations without option.
module React = {
  type element
  let null: element = %raw("null")
}

@react.component
let make = (~icon: React.element=?) => React.null
