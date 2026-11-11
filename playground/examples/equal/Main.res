type point = {x: int, y: int}
type shape = {name: string, corners: array<point>, label: option<string>}

let square = {
  name: "square",
  corners: [{x: 0, y: 0}, {x: 1, y: 0}, {x: 1, y: 1}, {x: 0, y: 1}],
  label: None,
}

Console.log(Equal.equal(square, {...square, label: None}))
Console.log(Equal.equal(square, {...square, corners: [{x: 0, y: 0}]}))
Console.log(Equal.equal({x: 1, y: 2}, {x: 1, y: 2}))
