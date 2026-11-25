// With every warning on, generated matches and binders report nothing:
// no non-exhaustive or redundant match (8, 11), no unused variable (26, 27).
@spice
type id = string

@spice
type ids = array<id>

@spice
type maybe = option<id>

@spice
type record = {id: id, ids: ids, maybe: option<int>, count?: int}

@spice
type variant = A | B(int) | C(id, ids)
