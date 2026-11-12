// A `@@config` inside a module, or a flag string in another attribute,
// configures nothing.
@@config({flags: ["-w", "-101-3"]})
@@deprecated("-bs-g")
@@warning("-bs-noassertfalse")

module M = {
  @@config({flags: ["-bs-g", "-bs-noassertfalse"]})
  type t = A(int) | B(string)
  let x = A(1)
  let fail = () => assert(false)
}

include {
  @@config({flags: ["-bs-g", "-bs-noassertfalse"]})
  let fail2 = () => assert(false)
}

let fail = () => assert(false)
