module Scale = {
  @spice
  type t = float
}

@spice
type t = {
  width: int,
  scale: Scale.t,
  label?: string,
}

@spice
type optional_t = option<t>

type view = t = {
  width: int,
  scale: Scale.t,
  label?: string,
}

@spice @genType
type ratio = [#A | #B | #C]

@spice
type preset = Small(int) | Large(int, string)

@spice @genType
type r = Auto | Preset(preset)

// A match that can fail names its place in the source, which a compile
// without locations cannot give: the unit is compiled again with them, and
// the check then runs on the located parse.
let small = (preset: preset) =>
  switch preset {
  | Small(size) => size
  }
