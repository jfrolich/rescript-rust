// error-output-parity: Typedecl.Type_clash from update_type after a duplicate method binds the stub manifest.
type rec t = {"x": t, "x": string}
