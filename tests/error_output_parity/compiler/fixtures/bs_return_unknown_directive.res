// error-output-parity: Bs_syntaxerr.Not_supported_directive_in_bs_return
@return(foo) @val external f: unit => option<int> = "f"
