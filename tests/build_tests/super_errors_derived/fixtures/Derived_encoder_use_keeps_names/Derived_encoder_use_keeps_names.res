@spice type values = array<JSON.t>
// A use of a derived encoder does not rename the argument’s element type, in any of the three modes.
type myjson = JSON.t
let takesMy = (x: myjson) => ignore(x)
let h = xs => {
  let r = values_encodeJson(xs)
  takesMy(r)
  xs
}
let _: string = h
