module type ListType = module type of List

let f1 = async () => {
  module M3 = await (List: ListType)
  module S = await Set
  M3.forEach
}
