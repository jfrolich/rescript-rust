type t<'a> = {mutable f: 'b. 'b => 'a}

let v: t<int> = {f: _ => 1}

let () = v.f = _ => 2

type id = {mutable g: 'a. 'a => 'a}

let w = {g: x => x}

let () = w.g = Obj.magic(x => x)
