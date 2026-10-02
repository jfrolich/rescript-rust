// error-output-parity: the second @@config pass runs after the builtin ppx warnings
@@config({
  flags: ["-103"],
})

let x = %raw(`1 +`)
