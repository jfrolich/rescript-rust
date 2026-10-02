// The spread base of a record expression must have the record type.
type t={x:int}
let value={()}
let updated={...value,x:2}
