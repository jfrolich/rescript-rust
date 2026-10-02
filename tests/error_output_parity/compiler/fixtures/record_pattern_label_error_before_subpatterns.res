// Record pattern labels are all disambiguated before the field patterns are
// typed: the unknown label is reported before the repeated variable.
type r = {x: int, z: int}
let f = ({x, z: x, y}: r) => x
