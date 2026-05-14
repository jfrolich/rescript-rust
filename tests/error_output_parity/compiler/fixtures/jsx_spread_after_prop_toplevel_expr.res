// error-output-parity: JSX v4 spread ordering is checked from top-level expressions too.
let props = {"className": "from-spread"}

Js.log(<div id="x" {...props} />)
