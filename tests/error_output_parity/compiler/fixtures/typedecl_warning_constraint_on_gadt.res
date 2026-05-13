// error-output-parity: Typedecl emits warning 62 for constraints on GADT type declarations.
@@warning("+62-34")

type rec t<'a> = A: t<int> constraint 'a = int
