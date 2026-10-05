// A record pattern with no known type picks the record that has every field
// (typecore.ml `disambiguate_label_by_ids`), not the latest record with the
// first field.
type scope = User | Workspace
type owner = {scope: scope, userID: string, orgID: string}
type row = {id: string, scope: scope, orgID: string}

let partition = ({scope, userID, orgID}) =>
  switch scope {
  | User => orgID ++ userID
  | Workspace => orgID
  }

// Labels qualified by a local module carry the module-qualified field types.
module Chat = {
  type clip = {id: string, name: string}
  type seek = {toTime: float => unit, clips: array<clip>}
}

let clips: array<Chat.clip> = [{id: "a", name: "A"}]
let seek = {Chat.toTime: _ => (), clips}
let firstClip = {Chat.id: "b", name: "B"}

let main = () => (partition({scope: User, userID: "u", orgID: "o"}), seek.clips, firstClip)
