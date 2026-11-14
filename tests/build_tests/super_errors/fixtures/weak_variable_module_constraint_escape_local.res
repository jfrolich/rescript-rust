// A weak variable of an earlier item cannot be instantiated, by a module
// constraint, to a type declared after it: the level update of the inclusion
// check fails, so the value does not match its specification.
// The weak variable and the module are local to a function body.
let f = () => {let r = ref(None)
module M: {type t
let v: option<t>} = {type t
let v = r.contents}
r.contents}
