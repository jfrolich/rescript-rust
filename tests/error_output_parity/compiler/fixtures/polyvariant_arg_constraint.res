// Polymorphic variant arguments accept a type constraint, like constructor arguments.
let f = x => #A(x: char)
let g: int = f('a')
