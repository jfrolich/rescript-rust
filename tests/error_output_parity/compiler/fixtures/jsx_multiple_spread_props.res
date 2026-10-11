// error-output-parity: JSX v4 rejects multiple spread props.
let props = {"className": "from-spread"}
let moreProps = {"id": "x"}

let element = <div {...props} {...moreProps} />
