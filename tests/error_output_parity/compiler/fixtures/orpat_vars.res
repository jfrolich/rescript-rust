// error-output-parity: Typecore.Orpat_vars
type value = A(int) | B

let result = switch A(1) {
| A(x) | B => x
}
