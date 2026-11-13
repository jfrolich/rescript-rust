type dialog = Closed | Editing | Saving | Broken
type event = Open | Save | Saved | SaveFailed | Cancel

let update = (dialog, event) =>
  switch (dialog, event) {
  | (Closed, Open) => Editing
  | (Editing, Save) => Saving
  | (Editing, Cancel) => Closed
  | (Saving, Saved) => Closed
  | (Saving, SaveFailed) => Broken
  | _ => dialog
  }

@spec
let canBeClosed: Spec.t<dialog, event> = {
  init: Closed,
  step: update,
  reachable: dialog => dialog == Closed,
}
