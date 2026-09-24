type a = private int
let y: a = Obj.magic(1)
let x1 = (y :> int)
let x2 = y :> int
let f = (v: int) => v
let x3 = f(y :> int)
let x4 = [y :> int]
let x5 = {
  let z = y
  z :> int
}
let x6 = switch 1 {
| _ => y :> int
}
let x7 = (y :> int, 1)
let x8 = Some(y :> int)
let x9 = if true { y :> int } else { 1 }
let x12 = list{(y :> int)}
