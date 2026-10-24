@spice.serde({legacyWrite: true})
type external_ =
  | Unit
  | @as("renamed") Renamed
  | Single(int)
  | Pair(string, bool)
  | Rec({a: string, b: option<int>})

// The same type in the default spice encoding, which legacyWrite must match.
@spice
type default =
  | Unit
  | Renamed
  | Single(int)
  | Pair(string, bool)
  | Rec({a: string, b: option<int>})

@spice.serde({legacyWrite: true}) @tag("type")
type internal =
  | Regular
  | Point({x: int, y: int})

@spice.serde({legacyWrite: true})
type poly = [#Left | #Payload(int) | #Pair(string, bool)]

@spice
type defaultPoly = [#Left | #Payload(int) | #Pair(string, bool)]

@spice.serde({legacyWrite: false})
type off = A | B(int)
