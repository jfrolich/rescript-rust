type rx = {x: int}
type ry = {y: string}
type rxy = {...rx, @uncurry ...ry}

let vxy: rxy = {x: 10, y: "abc"}
let bad: string = vxy
