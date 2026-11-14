// Every export of the module: types first, then the values.
module Api = %ts("./api.ts")

let activeTitles = async () => {
  let todos = await Api.list(#active)
  todos->Array.filter(todo => !todo.done)->Array.map(todo => todo.title)
}

let urgent = Api.create("Ship it", ~priority=High)

// One type under a name of your own.
type todo = %ts("./api.ts#Todo")
let draft: todo = {id: 0., title: "Draft", done: false}
