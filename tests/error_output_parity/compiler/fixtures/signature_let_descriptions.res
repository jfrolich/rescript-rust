module type S = {
  let x: int
  let \"y": string
  @attr let z: (int, int) => int
  let w: 'a. 'a => 'a
}
