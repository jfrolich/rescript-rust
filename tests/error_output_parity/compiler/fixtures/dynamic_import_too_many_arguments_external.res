// error-output-parity: Lam_compile dynamic import rejects extra primitive arguments.
external bad: (int, int) => promise<int> = "%import"
let x = bad(1, 2)
