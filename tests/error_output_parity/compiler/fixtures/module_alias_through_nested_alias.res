module E = {
  module X = {
    module Y = {
      module B = {
        let g = 3
        type t = int
      }
    }
    module Z = Y
  }
  module All = X
}
module C = E.All.Z.B
let v: C.t = C.g
module F = {
  module G = E.All
  module H = G.Z
}
let w = F.H.B.g + F.G.Y.B.g
let bad: string = C.g
