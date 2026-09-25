// A tagged template ends the primary expression; the call after it is parsed normally.
let sum: (int, int) => int = %raw`(a,b) => a + b
`()
