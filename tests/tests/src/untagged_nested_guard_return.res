// A switch on an @unboxed variant whose matched arm returns from a nested
// guarded switch keeps the else of the outer option check, as OCaml emits it.
@unboxed
type status = | @as("CREATED") Created | Other(string)
type upload = {status: status}

let f = (u: option<upload>, r: result<unit, string>) =>
  switch u {
  | Some({status: Created}) =>
    switch r {
    | Ok(_) => Ok()
    | Error(e) if e == "C" => Ok()
    | Error(e) => Error(e)
    }
  | Some(_) => Ok()
  | None =>
    Console.log("nf")
    Error("x")
  }
