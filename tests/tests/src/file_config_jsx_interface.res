// `-bs-jsx` in an interface's `@@config` rewrites its components too.
@@config({flags: ["-bs-jsx", "4"]})

@react.component
let make = (~name: string) => React.string(name)
