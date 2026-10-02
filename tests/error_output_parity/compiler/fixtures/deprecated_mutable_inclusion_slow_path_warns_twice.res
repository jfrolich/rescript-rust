// includecore compare_records re-runs its field loop after the fast Ctype.equal fails, so the deprecated-mutable warning is printed again.
@@warning("+3-32-34")

module M: {
  type t = {
    mutable x: int,
  }
} = {
  type t = {
    @deprecated_mutable("use setX")
    mutable x: float,
  }
}
