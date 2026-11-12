// CHECKER_REDESIGN.md I.2.4: comparison through a stored interface.
let g = p => { ignore(Checker_identity_comparison_b.k(p)); p > Checker_identity_comparison_a.Green }
let h = q => { ignore(q == Checker_identity_comparison_a.x); q > Checker_identity_comparison_a.Green }
