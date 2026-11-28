// Not true: `+` wraps around at the largest int.
@law
let successorIsLarger = (n: int) => n + 1 > n

// True, and the prover does not find out: it knows `+` and `<=`,
// not how the two go together.
@law
let doubleIsEven = (n: int) => mod(n + n, 2) == 0
