(** Canonicalize ident stamps in typed trees.

    Rewrites all ident stamps to sequential canonical values (1, 2, 3, ...)
    based on first-occurrence order. This makes comparison insensitive
    to stamp allocation order while preserving identity/sharing patterns.

    Stamps <= 0 (persistent, hidden) are left unchanged. *)
