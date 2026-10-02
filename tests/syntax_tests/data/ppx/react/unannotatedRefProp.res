@@jsxConfig({version: 4})

module V4C = {
  @react.component
  let make = (~id: option<string>=?, ~ref=?, ~label: string) => {
    let _ = id
    let _ = ref
    React.string(label)
  }
}
