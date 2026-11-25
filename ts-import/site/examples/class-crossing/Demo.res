// Two packages, each with its own declaration of an options object
// and of an enum.
module A = {
  type options = {capture: bool, once: bool}
  type mode = | @as("open") Open | @as("closed") Closed
}

module B = {
  type options = {capture: bool}
  type mode = | @as("open") Open | @as("closed") Closed
  external listen: (options, mode) => unit = "listen"
}

// The declarations describe the same values, so `:>` goes from one to
// the other.
let listen = (options: A.options, mode: A.mode) =>
  B.listen((options :> B.options), (mode :> B.mode))
