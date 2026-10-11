// error-output-parity: @@config flags use the same warning parser as bsc CLI flags.
@@config({flags: ["-warn-error", "+A"]})

let f = x => {
  let unused = x
  1
}
