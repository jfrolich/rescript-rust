// error-output-parity: Typedecl.Parameters_differ object polymorphic recursion
type rec foo<'v> = {"fmap": 'b. ('v => 'b) => foo<'b>}
