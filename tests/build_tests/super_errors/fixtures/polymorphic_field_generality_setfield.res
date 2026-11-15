type t<'a> = {mutable f: 'b. 'b => 'a}
let v: t<int> = {f: _ => 1}
let () = v.f = y => y
