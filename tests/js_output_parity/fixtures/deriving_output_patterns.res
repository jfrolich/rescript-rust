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

type config = {
  name: string,
  count: int,
  transform?: int => int,
}

type lightConfig = {
  enabled: bool,
  label?: string,
}

let pointValue = {x: 2, y: 3}

let configValue = {name: "root", count: 4, transform: value => value + 1}

let lightValue = {enabled: true, label: "visible"}

let actionValue = Pair((5, "five"))

let allValues = (
  x(pointValue) + y(pointValue),
  add(3),
  rename("next"),
  pair((1, "one")),
  actionValue,
  configValue.name,
  configValue.count,
  switch configValue.transform {
  | Some(transform) => transform(9)
  | None => 0
  },
  lightValue.enabled,
  lightValue.label,
)
