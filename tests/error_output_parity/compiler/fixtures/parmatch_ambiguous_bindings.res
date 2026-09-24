type r = {a: int, b: int}
type s = {b: int}
let f = (x: r) => switch x { | {a, ...s as rest} if rest.b > a => 1 | _ => 2 }
let g = x => switch x { | (Some(y), _) | (_, Some(y)) if y > 0 => 1 | _ => 2 }
let h = x => switch x { | (Some(y), None) | (None, Some(y)) if y > 0 => 1 | _ => 2 }
