// The types come from the checker, not from the syntax. `Partial`, `Omit`,
// mapped and template literal types and inferred results are all
// evaluated before ReScript sees them.
let {update, setters, snapshot} = %ts("./settings.ts")

let dark = update({theme: #dark, fontSize: 16.})
setters.setTheme(#light)
setters.setWrap(false)

let saved = snapshot()
let size = saved.settings.fontSize
let year = saved.savedAt->Date.getFullYear
