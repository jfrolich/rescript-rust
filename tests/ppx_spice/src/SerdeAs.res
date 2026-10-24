// ReScript's @as renames a constructor in memory and, with @spice.serde, in JSON.

@spice.serde
type external_ = | @as("unit") Unit | @as("one") One(int) | Plain

@spice.serde @tag("type")
type internal =
  | @as("reg") Regular
  | @as("full") Full({screenFit: string})
  | @as("same") @spice.as("same") Both
