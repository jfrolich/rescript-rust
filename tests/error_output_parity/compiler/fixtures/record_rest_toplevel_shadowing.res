type s = {id: string, v: int}
type r = {v: int}
let {id: _, ...r as value} = {id: "x", v: 1}
let {id: _, ...r as value} = {id: "x", v: 1}
let _ = value
let x: int = "a"
