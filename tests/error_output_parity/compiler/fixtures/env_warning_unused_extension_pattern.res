// error-output-parity: Env warning 38 notes exceptions that are only used in patterns.
module type S = {}

module M: S = {
  exception Unused

  let check = value =>
    try {
      value
    } catch {
    | Unused => true
    | _ => false
    }
}
