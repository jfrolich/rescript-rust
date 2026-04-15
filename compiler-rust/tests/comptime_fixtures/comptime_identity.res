type point = {
  x: int,
  y: int,
}

@comptime
let getX = (p: point) => p.x

let p: point = {x: 10, y: 20}
let result = getX(p)
