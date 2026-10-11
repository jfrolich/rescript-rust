// Ppat_interval raises Invalid_interval before typing the constants.
let value = switch "" {
| 1 .. 3 => true
| _ => false
}
