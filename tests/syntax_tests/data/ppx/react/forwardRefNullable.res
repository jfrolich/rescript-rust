module NullableT = {
  @react.component
  let make = React.forwardRef((~id: string, ~children=?, ref: Nullable.t<React.ref<Nullable.t<Dom.element>>>) => {
    ignore(ref)
    <div id> {children->Option.getOr(React.null)} </div>
  })
}

module StdlibNullableT = {
  @react.component
  let make = React.forwardRef((~id: string, ref: Stdlib.Nullable.t<React.ref<Nullable.t<Dom.element>>>) => {
    ignore(ref)
    <div id />
  })
}

module LowercaseNullable = {
  @react.component
  let make = React.forwardRef((~id: string, ref: nullable<React.ref<Nullable.t<Dom.element>>>) => {
    ignore(ref)
    <div id />
  })
}
