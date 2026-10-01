// Coercing a field bound from a variant-spread inline record. The coerced
// type's node is shared through the nullary abbreviation memo, as in OCaml.
type sceneID = string
module Combined = {
  type t = UpdateArtboardBackground({storyID: string, sceneID: sceneID})
}
module Event = {
  type t =
    | ...Combined.t
    | DeleteScene({sceneID: sceneID})
}
type wireEvent = UpdateW({sceneID: string})
let f = (event: Event.t) =>
  switch event {
  | UpdateArtboardBackground({storyID: _, sceneID}) => UpdateW({sceneID: (sceneID :> string)})
  | DeleteScene({sceneID}) => UpdateW({sceneID: (sceneID :> string)})
  }
