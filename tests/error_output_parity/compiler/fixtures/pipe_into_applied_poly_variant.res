type a = A | B
type b = | ...a | C
let f = x => x->(#close(1))
let g = x => x->#close
let h = x => x->Some
