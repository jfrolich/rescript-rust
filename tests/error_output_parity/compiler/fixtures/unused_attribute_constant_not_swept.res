// Attributes on constant expressions are not swept.
let x = @as("a") 1
type p = @as("x") int
