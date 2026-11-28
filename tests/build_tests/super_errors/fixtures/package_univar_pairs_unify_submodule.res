module type T = {
  module M: {
    let x: int
  }
}
module type S = {
  module M: {
    let x: int
  }
}
let g = (o: {"f": 'a. (module(S), 'a)}): {"f": 'a. (module(T), 'a)} => o
