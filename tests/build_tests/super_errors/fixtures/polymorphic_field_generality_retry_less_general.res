type t = {f: 'a. 'a => unit}
let v = {f: (() => _ => ())()}
