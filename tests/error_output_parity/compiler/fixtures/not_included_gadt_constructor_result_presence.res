// error-output-parity: Includecore.compare_variants GADT constructor result presence mismatch
module M: {
  type rec t<'a> = | Int
} = {
  type rec t<'a> = | Int: t<int>
}
