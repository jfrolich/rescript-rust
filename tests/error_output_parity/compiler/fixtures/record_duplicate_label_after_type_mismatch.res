// check_duplicates runs after the record type is unified with the expected type.
type value = {x: int}

let result: result<int, string> = {x: 1, x: 2}
