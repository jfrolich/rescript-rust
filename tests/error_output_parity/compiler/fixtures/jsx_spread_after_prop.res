// error-output-parity: JSX v4 requires a spread prop to appear before named props.
let props = {"className": "from-spread"}

let element = <div id="x" {...props} />
