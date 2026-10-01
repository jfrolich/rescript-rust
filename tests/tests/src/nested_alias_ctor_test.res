// A constructor disambiguated through a local alias of a nested module of
// another unit is typed at the alias's component path (`Combi.t`).
module Combi = Nested_alias_ctor_types.Structured.Combi.Landscape
let name = Combi.toName(CameraBubble({cameraSize: 1, screenStyle: Regular}))
