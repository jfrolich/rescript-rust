type e = ..
module type T = {
  type e += A
}
module type S = {
  type e += A
}
let g = (o: {"f": 'a. (module(S), 'a)}): {"f": 'a. (module(T), 'a)} => o
