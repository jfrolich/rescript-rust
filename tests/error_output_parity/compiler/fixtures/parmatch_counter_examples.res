type r = {a: int, b?: string, c: bool}
let f1 = (x: r) => switch x { | {a: 1, c: true} => 1 }
let f2 = (x: option<option<int>>) => switch x { | Some(Some(_)) => 1 | None => 2 }
let f3 = (x: (bool, bool)) => switch x { | (true, _) => 1 | (_, true) => 2 }
let f4 = (x: [#A | #B(int) | #C]) => switch x { | #A => 1 | #B(1) => 2 }
let f5 = (x: list<int>) => switch x { | list{} => 0 | list{_, _} => 1 }
let f6 = (x: array<int>) => switch x { | [] => 0 | [_] => 1 }
let f7 = (x: string) => switch x { | "a" => 1 | "b" => 2 }
let f8 = (x: char) => switch x { | 'a' => 1 }
let f9 = (x: float) => switch x { | 1.0 => 1 }
let f10 = (x: int) => switch x { | 0 | 1 => 0 | 1 => 2 | _ => 3 }
let f11 = (x: option<int>) => switch x { | Some(n) if n > 0 => n | None => 0 }
let f12 = (x: option<int>) => switch x { | Some(n) if n > 0 => n }
let f13 = (x: r) => switch x { | {b: ?None} => 1 }
let f14 = (x: bigint) => switch x { | 1n => 1 }
let f15 = x => switch x { | (Some(_), Ok(_)) => 1 | (None, Error(_)) => 2 }
let f16 = (x: result<int, string>) => switch x { | Ok(1) | Ok(2) => 1 | Ok(2) | Error(_) => 2 | Ok(_) => 3 }
let {a} = {a: 1, c: true}
let Some(z) = Some(1)
let f17 = (Some(q)) => q
