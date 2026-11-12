// The flags before an unknown one still apply, the ones after it do not
// (Bsc_args.parse_exn stops at the first error).
@@config({flags: ["-w", "-22", "-bs-no-version-header", "-bogus", "-noassert"]})

let checked = x => {
  assert(x > 0)
  x
}
