// error-output-parity: Warning 3 for using a deprecated type.
@@warning("+3-34")

@deprecated
type stale = int

type fresh = stale
