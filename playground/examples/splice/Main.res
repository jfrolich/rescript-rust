type point = {x: float, y: float}
type storedPoint = {key: string, version: int, x: float, y: float}

let point = {x: 3.0, y: 4.0}

// {key: "p1", version: 1, x: point.x, y: point.y}
let stored: storedPoint = Splice.withKey(point, "p1")
Console.log(stored)

// distance(point.x, point.y)
let distance = (x, y) => Math.sqrt(x *. x +. y *. y)
Console.log(Splice.call(distance, point))

type level = Debug | Info | Warning | Error

// One case per constructor, then the case of the quote.
let level: option<level> = Splice.parse("Warning")
let unknown: option<level> = Splice.parse("loud")
Console.log2(level, unknown)
