type r = {a: int, b?: int}
let f = x => switch x { | {@attr a} => a }
let g = x => switch x { | {?b, _} => b }
let h = (d: dict<int>) => switch d { | dict{"a": 1, "b": ?c} => 1 | _ => 2 }
let k = x => switch x { | {a: 1, _, b: ?None} => 1 | _ => 2 }
