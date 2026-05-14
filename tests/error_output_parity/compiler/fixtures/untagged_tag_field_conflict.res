// error-output-parity: Ast_untagged_variants.TagFieldNameConflict
@tag("name")
type t = A({name: string})
