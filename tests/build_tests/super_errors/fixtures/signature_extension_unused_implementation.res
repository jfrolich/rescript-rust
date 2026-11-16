// An implementation's extension constructor keeps its unused warning in
// each of its three forms.
module M: {} = {
  exception E
}

module M2: {
  let f: exn => int
} = {
  exception E

  let f = x =>
    switch x {
    | E => 1
    | _ => 0
    }
}

type t = ..

module M3: {
  type t += private E
} = {
  type t += E
}
