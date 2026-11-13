@spice type values = array<JSON.t>

type myjson = JSON.t
let takesMy = (x: myjson) => ignore(x)
let h = xs => {
  let r = values_encodeJson(xs)
  takesMy(r)
  xs
}
let _: string = h
