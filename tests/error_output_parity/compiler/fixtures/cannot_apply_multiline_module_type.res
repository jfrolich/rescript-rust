// error-output-parity: Cannot_apply puts a multi-line module type after its break
module M = {
  let getLight = (x: string) => x
  let other = 1
}
module N = M(M)
