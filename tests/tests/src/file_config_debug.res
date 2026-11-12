// The first leading `@@config` applies its flags after the command line's.
@@warning("-101")
@@config({flags: ["-bs-g", "-bs-noassertfalse"]})
@@config({flags: ["-bs-no-version-header"]})

type t = A(int) | B(string)

let x = A(1)
let fail = () => assert(false)
