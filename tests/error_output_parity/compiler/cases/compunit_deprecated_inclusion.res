// error-output-parity: Warning 3 when a deprecated implementation value satisfies a .resi.
@@warning("+3-32-34-60")

@deprecated("use y")
external x: int => int = "%identity"
