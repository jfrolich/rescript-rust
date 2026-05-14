// error-output-parity: Lam_compile dynamic import rejects unit-valued primitive argument.
external bad: unit => promise<int> = "%import"
let x = bad()
