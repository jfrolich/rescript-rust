module Types = {
  type config = {shortcuts: array<int>, origin: int}
  type entry = {enabled: bool, shortcut: option<config>, name: string}
}
let x = 1
open Types
let use = (~enabled, ~name, ~origin, ~shortcut) => {
  let shortcutConfig = switch shortcut {
  | Some(x) => Some({shortcuts: [x], origin})
  | None => None
  }
  let entry = {
    enabled,
    shortcut: shortcutConfig,
    name,
  }
  entry
}
