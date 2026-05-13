// error-output-parity: Ast_external_process preserves duplicate @module state for conflict reporting.
@module @module("pkg") external f: int = "x"
