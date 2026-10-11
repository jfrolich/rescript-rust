type rx = {x: int}
type ry = {y: string}
type rxi = {...rx, i?: int}
type rxy = {...rx, ...ry}

let xxi = {x: 10}
let bad: string = xxi
