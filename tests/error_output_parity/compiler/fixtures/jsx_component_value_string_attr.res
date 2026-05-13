// error-output-parity: JSX component value props leave unused @string to the invariant warning sweep.
module React = {
  type element = int
  let null = 0
}

@react.component
let make = (~_kind: @string [#a]) => React.null
