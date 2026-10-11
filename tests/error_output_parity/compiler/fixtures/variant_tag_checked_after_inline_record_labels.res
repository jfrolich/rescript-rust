// @tag is validated after the declarations are translated; without spreads the
// duplicate inline-record field is reported first.
@tag(1)
type t = A({x: int, x: int})
