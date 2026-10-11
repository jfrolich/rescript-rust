// OCaml reaches Misc.fatal_error "Matching.comp_exit" here; Rust reports it the same way.
let _ = switch (Some(1), Some(2)) {
| _ => 0
| (Some(x), _) | (_, Some(x)) when x > 0 => 1
}
