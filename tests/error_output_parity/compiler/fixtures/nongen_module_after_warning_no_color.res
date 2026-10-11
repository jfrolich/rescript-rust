// A warning printed before the non-generalizable module error turns off the
// message style tags (Misc.Color setup).
let foo = 1

module M = {
  let foo = dict{}
}

let _ = foo
open M
let _ = foo