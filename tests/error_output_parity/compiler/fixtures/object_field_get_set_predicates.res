type t = {@get({null: true, null: true}) "value": int}
type u = {@get({null: false}) "a": int, @get(undefined) "b": int, @get(nullable) "c": int, @set "d": int, @set({no_get: false}) "e": int, @set({no_get}) "f": int}
let f = (x: u) => (x["a"], x["b"], x["c"], x["d"], x["e"])
let g = (x: t) => x["value"]
