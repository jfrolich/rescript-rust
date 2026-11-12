type shape
type point
let point_encode: point => JSON.t
let point_decode: JSON.t => Spice.result<point>
