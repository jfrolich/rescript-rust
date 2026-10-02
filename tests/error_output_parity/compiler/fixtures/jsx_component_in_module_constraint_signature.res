module React = {
  type element = unit
  let null = ()
}
module Foo: {
  @react.component let make: (~x: int) => React.element
} = {
  let make = (~x as _) => React.null
}
