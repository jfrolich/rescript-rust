let {distance} = %ts("./geometry.ts")

let origin = {x: 0., y: 0.}

// `y` is missing and `x` is a string: ReScript reports it here, at the call,
// with the types TypeScript declared.
let d = distance(origin, {x: "3"})
