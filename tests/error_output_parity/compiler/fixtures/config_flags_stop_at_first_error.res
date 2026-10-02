@@config({flags: ["-w", "+A", "-bogus", "-w", "-A"]})
let f = x => switch x { | Some(_) => 1 }
let x = 1
