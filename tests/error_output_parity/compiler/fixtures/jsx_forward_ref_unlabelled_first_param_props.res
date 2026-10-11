// A forwardRef component whose first parameter is an unlabelled non-ref variable has no props.
@react.component
let make = React.forwardRef(( ( right),~value) => value)
