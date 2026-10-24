// Types of a nested module, re-exported by NestedModuleAlias through an
// alias of `NestedTypes.Transcript`.
module Transcript = {
  @genType
  type word = {index: int, text: string}

  @genType
  type data = {words: array<word>}
}
