// error-output-parity: External_ffi_types rejects empty import bind names.
@module(("pkg", "")) external f: int => int = "x"
