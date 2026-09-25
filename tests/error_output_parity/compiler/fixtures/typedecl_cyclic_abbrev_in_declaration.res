// Typedecl.transl_declaration rejects a cyclic manifest with
// Ctype.cyclic_abbrev before the well-foundedness checks.
type rec t = u and u = u
