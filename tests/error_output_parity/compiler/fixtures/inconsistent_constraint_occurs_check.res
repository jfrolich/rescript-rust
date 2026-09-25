// Inconsistent_constraint prints the full unification report after `@.`,
// including the occurs-check explanation.
type hidden<'a> = ..
type t<+'a> = array<'a> constraint 'a = hidden<'a>
