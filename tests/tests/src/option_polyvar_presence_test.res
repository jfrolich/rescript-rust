// An option of a tagless polymorphic variant keeps its presence test when the
// first case compares the payload with a variant name.
type medium = [#Camera | #Screen | #Upload]

let pick = (m: option<medium>) =>
  switch m {
  | Some(#Camera) => [1]
  | _ => [2]
  }

let pickGuarded = (m: option<medium>, n: option<int>) =>
  switch (m, n) {
  | (Some(#Screen), Some(k)) if k > 0 => [k]
  | _ => []
  }

// A numeric-looking name is a number at runtime, so its comparison already
// rules out undefined.
let pickNumeric = (m: option<[#1 | #2]>) =>
  switch m {
  | Some(#1) => [1]
  | _ => [2]
  }
