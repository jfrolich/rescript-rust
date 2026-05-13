// error-output-parity: Typecore.Orpat_vars spellcheck hint
type value = A(int) | B(int)

let result = switch A(1) {
| A(firstName) | B(fristName) => firstName
}
