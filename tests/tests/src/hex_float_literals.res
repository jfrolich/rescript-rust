// Hexadecimal float literals: OCaml float_of_string (subnormals, rounding
// past 53 bits) and Js_number.to_string (63-bit ints, %.12g/%.15g/%.18g).
let a = 0x1p-1074
let b = 0x1.00000000000008p0
let c = 0x1.00000000000018p0
let d = 0x123456789abcdef12p0
let e = 0x1p-1075
let f = 0x1.8p-1074
let g = 0x0.0000000000001p-1022
let h = 0x1.fffffffffffff8p1023
let c2 = 0x1p62
let c3 = 0x1.8p62
let c4 = -0x1p62
@unboxed type t = @as(0x1p-1074) A | @as(0.) B
let t = (x: t) => switch x { | A => 1 | B => 2 }
