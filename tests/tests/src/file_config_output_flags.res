// `@@config` flags that change the generated JavaScript: no version header,
// no division-by-zero checks, no assertion checks.
@@config({flags: ["-bs-no-version-header", "-bs-no-check-div-by-zero", "-noassert"]})

let div = (a, b) => a / b
let rem = (a, b) => mod(a, b)
let bigDiv = (a: bigint, b) => a / b
let bigRem = (a: bigint, b) => mod(a, b)

let checked = x => {
  assert(x > 0)
  x
}
