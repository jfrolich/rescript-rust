// error-output-parity: Typecore.Expr_type_clash optional arrow arg hidden type
let test: (int, int) => int = (~x=?, y) => y
