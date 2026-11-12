// CHECKER_REDESIGN.md I.2.4: comparison through a stored interface.
let k = a => { ignore(a == Checker_identity_comparison_a.x); Checker_identity_comparison_a.takesId(a); a }
