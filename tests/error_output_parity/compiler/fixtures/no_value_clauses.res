// error-output-parity: Typecore.No_value_clauses
let raiseNotFound = () => raise(Not_found)

let value = switch raiseNotFound() {
| exception Not_found => 0
}
