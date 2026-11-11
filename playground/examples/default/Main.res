type theme = Light | Dark | Custom(string)

type settings = {
  name: string,
  retries: int,
  verbose: bool,
  tags: array<string>,
  theme: theme,
  proxy: option<string>,
}

let initial: settings = Default.value()

Console.log(initial)
Console.log({...initial, name: "production", retries: 3})
