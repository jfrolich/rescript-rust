type exactArrayLike<'a> = Stdlib_Array.arrayLike<'a>
type qualifiedArrayLike<'a> = Stdlib.Array.arrayLike<'a>

external exactIdentity: exactArrayLike<'a> => exactArrayLike<'a> = "%identity"
external qualifiedIdentity: qualifiedArrayLike<'a> => qualifiedArrayLike<'a> = "%identity"

let exactMake = Stdlib_Array.make(~length=2, None)
exactMake[0] = Some(1)

let qualifiedMake = Stdlib.Array.make(~length=2, None)
qualifiedMake[0] = Some(2)

let exactUse = (value: exactArrayLike<'a>) => value->exactIdentity
let qualifiedUse = (value: qualifiedArrayLike<'a>) => value->qualifiedIdentity
