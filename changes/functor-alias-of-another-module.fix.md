- Type checker: an alias of a functor declared in another file can be applied
  (`module S = Other.AliasSet(Other.IntOrd)` for `module AliasSet = MakeSet`
  in `Other`), as in the OCaml compiler, instead of failing with "This module
  is not a functor".
