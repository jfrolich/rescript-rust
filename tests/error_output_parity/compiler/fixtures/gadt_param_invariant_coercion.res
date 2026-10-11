type rec kind<_> = Float: kind<float>
let f = (x: kind<[#a]>) => (x :> kind<[#a | #b]>)
