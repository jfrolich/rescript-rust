// error-output-parity: Typecore emits warning 9 for non-closed record patterns.
type t = {x: int, y: int}

let value = {x: 1, y: 2}

let result = switch value {
| {x} => x
}
