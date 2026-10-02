// The scrutinee type is generalized; the case patterns still must agree.
let _ = switch %raw("1") {
| 1 => 0
| (2, 1) => 1
| _ => 2
}
