// Applies an alias of a functor declared in another file.
module FromOtherAlias = Functor_alias_source.AliasSet(Functor_alias_source.IntOrd)
let d = FromOtherAlias.add(1)
