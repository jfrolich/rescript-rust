// error-output-parity: a record field path cannot define multiple inline records.
type options = {
  extra?: {
    name: result<{first: bool}, {second: bool}>,
  },
}
