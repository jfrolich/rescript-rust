module type S = {}
let f = x => switch x { | module(M) => 0 }
