@instanceOf("Set")
type t<'a>

@pure
external asIterable: t<'a> => Stdlib_Iterable.t<'a> = "%identity"

@pure @new external make: unit => t<'a> = "Set"
@pure @new external fromArray: array<'a> => t<'a> = "Set"
@pure @new external fromIterable: Stdlib_Iterable.t<'a> => t<'a> = "Set"

@pure @get external size: t<'a> => int = "size"

let isEmpty = set => set->size === 0

@mutates @send external clear: t<'a> => unit = "clear"

@mutates @send external add: (t<'a>, 'a) => unit = "add"
@mutates @send external delete: (t<'a>, 'a) => bool = "delete"
@pure @send external has: (t<'a>, 'a) => bool = "has"

@pure @send external forEach: (t<'a>, 'a => unit) => unit = "forEach"

@send external values: t<'a> => Stdlib_IteratorObject.t<'a, unit, unknown> = "values"

@pure @send external difference: (t<'a>, t<'a>) => t<'a> = "difference"
@pure @send external intersection: (t<'a>, t<'a>) => t<'a> = "intersection"
@pure @send external union: (t<'a>, t<'a>) => t<'a> = "union"
@pure @send external symmetricDifference: (t<'a>, t<'a>) => t<'a> = "symmetricDifference"
@pure @send external isSubsetOf: (t<'a>, t<'a>) => bool = "isSubsetOf"
@pure @send external isSupersetOf: (t<'a>, t<'a>) => bool = "isSupersetOf"
@pure @send external isDisjointFrom: (t<'a>, t<'a>) => bool = "isDisjointFrom"

@pure
external toArray: t<'a> => array<'a> = "Array.from"

@pure
external ignore: t<'a> => unit = "%ignore"
