// error-output-parity: Bs_syntaxerr.Illegal_attribute for @module payload arity.
@module(("a", "b", "c")) external f: int = "f"
