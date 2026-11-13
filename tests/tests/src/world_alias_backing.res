// Abstract types reached through both a namespace alias and a child alias.
type item
module Sub = {
  type t = item
  @val external make: int => t = "makeWorldAliasItem"
  let id = (x: t) => x
}
