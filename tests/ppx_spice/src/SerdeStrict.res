// @spice.serde without {legacy: true}: decoders read only the serde form.

@spice.serde
type poly = [#Left | #Payload(int)]

@spice.serde
type external_ = Unit | Single(int)

@spice.serde @tag("type")
type internal = Regular | Overlap({size: int})
