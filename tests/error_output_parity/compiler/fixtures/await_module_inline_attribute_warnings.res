// error-output-parity: transl_module checks @inline on every level of an awaited module.
@@warning("+53")
let f = async () => {
  module M3 = await @inline List
  M3.forEach
}
