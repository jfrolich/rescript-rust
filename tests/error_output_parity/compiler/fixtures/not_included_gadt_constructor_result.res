// error-output-parity: Includecore.compare_variants GADT constructor result mismatch
module M: {
  type rec t<'a> = | Int: t<int>
} = {
  type rec t<'a> = | Int: t<string>
}
