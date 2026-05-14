@deriving(accessors)
type point = {
  x: int,
  y: int,
}

@deriving(accessors)
type action =
  | Add(int)
  | Rename(string)
  | Pair((int, string))

@deriving(abstract)
type config = {
  name: string,
  count: int,
  @optional transform: int => int,
}

@deriving({abstract: light})
type lightConfig = {
  enabled: bool,
  @optional label: string,
}

let pointValue = {x: 2, y: 3}

let configValue = config(~name="root", ~count=4, ~transform=value => value + 1, ())

let lightValue = lightConfig(~enabled=true, ~label="visible", ())

let actionValue = Pair((5, "five"))

let allValues = (
  x(pointValue) + y(pointValue),
  add(3),
  rename("next"),
  pair((1, "one")),
  actionValue,
  nameGet(configValue),
  countGet(configValue),
  switch transformGet(configValue) {
  | Some(transform) => transform(9)
  | None => 0
  },
  enabled(lightValue),
  label(lightValue),
)
