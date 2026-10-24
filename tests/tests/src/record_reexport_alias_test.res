// Re-exporting a record whose field types go through a local alias of the
// original field type: the definitions are equal once the alias is expanded.
module Item = {
  type item = {id: string}
  type itemsResponse = {items: array<item>}
}

type item = Item.item
type itemsResponse = Item.itemsResponse = {items: array<item>}

let ids = ({items}: itemsResponse) => items->Array.map(item => item.id)
