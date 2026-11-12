// Only the first `@@config` among the leading attributes is read: the
// second one here, and the one after the type, change nothing.
@@config({flags: ["-w", "-101"]})
@@config({flags: ["-bs-g", "-bs-noassertfalse", "-bs-no-version-header"]})

type t = A(int) | B(string)

@@config({flags: ["-bs-g", "-bs-noassertfalse"]})

let x = A(1)
let y = B("y")
let fail = () => assert(false)
