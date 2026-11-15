module type Sig = {
  let x: int
}
module M: Sigg = {
  let x = 1
}
