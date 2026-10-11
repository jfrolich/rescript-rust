// error-output-parity: Typedecl warning 62 for constraints on GADT declarations in signatures.
@@warning("+62-34")

type rec t<'a> = A: t<int> constraint 'a = int
