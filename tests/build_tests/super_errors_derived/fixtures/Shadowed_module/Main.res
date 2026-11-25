// The generated decoder calls `Option.getOr`, which this module lacks.
module Option = {
  let map = (o, f) =>
    switch o {
    | Some(x) => Some(f(x))
    | None => None
    }
}

@spice
type r = {a: int}
