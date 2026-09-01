type qualifiedArrayLike<'a> = Stdlib.Array.arrayLike<'a>
type exactArrayLike<'a> = Stdlib_Array.arrayLike<'a>

external qualifiedIdentity: qualifiedArrayLike<'a> => qualifiedArrayLike<'a> = "%identity"
external exactIdentity: exactArrayLike<'a> => exactArrayLike<'a> = "%identity"

let qualifiedMake = Stdlib.Array.make(~length=2, None)
qualifiedMake[0] = Some(1)

let exactMake = Stdlib_Array.make(~length=2, None)
exactMake[0] = Some(2)

let qualifiedUse = (value: qualifiedArrayLike<'a>) => value->qualifiedIdentity
let exactUse = (value: exactArrayLike<'a>) => value->exactIdentity
