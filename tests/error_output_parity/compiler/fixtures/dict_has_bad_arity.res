// error-output-parity: Lam_compile_primitive rejects bad %%dict_has external arity.
external bad: unit => bool = "%dict_has"
let x = bad()
