@pure
let twice = (f, x) => f(f(x))

@pure
let squares = xs => xs->Array.map(x => x * x)

// The argument is checked here, where it is written.
@pure
let fourth = x => twice(n => n * n, x)
