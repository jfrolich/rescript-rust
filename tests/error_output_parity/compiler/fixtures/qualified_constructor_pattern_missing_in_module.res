// Differential fuzzer regression.
module N = {}
let f = x => switch x { | N.None => 1 | _ => 2 }
