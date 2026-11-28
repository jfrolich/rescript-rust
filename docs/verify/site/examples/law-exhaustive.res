type light = Red | Amber | Green

let next = light =>
  switch light {
  | Red => Green
  | Green => Amber
  | Amber => Red
  }

@law
let deMorgan = (a: bool, b: bool) => !(a && b) == (!a || !b)

@law
let threeStepsComeBack = (light: light) => next(next(next(light))) == light

@law
let neverStays = (light: light) => next(light) != light
