// Only the last declaration's @deriving attributes are processed.
@deriving(accessors) @deriving(accessors)
type rec a = {x: int}
@deriving(nope)
and b = {y: int}
