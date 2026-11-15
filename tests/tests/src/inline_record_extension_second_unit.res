// The inline record of an extension constructor of another unit.

let e = Inline_record_extension_lib.E({v: 1})
let c = Inline_record_extension_lib.C({v: 2})

let f = x =>
  switch x {
  | Inline_record_extension_lib.E({v}) => v
  | _ => 0
  }
