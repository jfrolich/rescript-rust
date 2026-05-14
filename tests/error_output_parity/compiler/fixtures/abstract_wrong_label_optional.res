// error-output-parity: Typecore.Abstract_wrong_label optional label branch
let test: (int, int) => int = (x, ~y=?) => y
