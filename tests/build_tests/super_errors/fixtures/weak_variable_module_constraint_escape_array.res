// A weak variable of an earlier item cannot be instantiated, by a module
// constraint, to a type declared after it: the level update of the inclusion
// check fails, so the value does not match its specification.
// The weak variable is an array element.
let r = ref([])
module M: {type t
let v: array<t>} = {type t
let v = r.contents}
let later = r.contents
