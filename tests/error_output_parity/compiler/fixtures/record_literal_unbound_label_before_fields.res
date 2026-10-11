// Pexp_record: with no concrete record expected type, process_label rejects a
// label that has nothing in scope before any field is typed.
type t = {one: bool, two: int}

let v = {
  one: true,
  two: "",
  three: "hello",
}
