type a = {mutable x: int}
type b = {mutable y: int}
let f = (v: b) => v.x = 1
let g = v => { v.y = 1; v.x = 2 }
