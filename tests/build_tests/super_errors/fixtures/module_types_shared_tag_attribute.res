// Inline record payloads with a shared @tag attribute (copied to each
// constructor) and its name in the variant layout count once.
module M: {
  @tag("kind") type t = T0({x: int})
  let v: string
} = {
  @tag("kind") type t = T0({x: int})
  let v = 1
}
