let rename = (old, next, log, save) => {
  if next != "" {
    if old != next {
      log(next)
      save(next)
    }
  }
}
let claim = async (value: nullable<string>, get) => {
  if value != Nullable.null {
    "ready"
  } else {
    let result = await get()
    result == "yes" ? "done" : "pending"
  }
}
let guard = (current, get, notify) => {
  if current() {
    let result = get()
    if result { notify() }
  }
}
let internal = (bypass, email) => {
  bypass() || email->String.endsWith("@example.com") || email->String.endsWith("@example.org")
}
let renameClosure = (old, log, save, blur, get) => {
  let set = name => {
    if old != name { log(name); save(name) }
  }
  _ => {
    blur()
    let name = get()
    if name != "" { set(name) }
  }
}
let testEmail = email => email->String.endsWith("@example.com") || email->String.endsWith("@example.org")
let test = (bypass, email) => bypass() || testEmail(email)
let asyncGuard = async (current, get, notify) => {
  if current() { let r = await get(); notify(r) }
}
type status = {name: string}
let optionClaim = async (value: nullable<string>, get) => {
  switch value->Nullable.toOption {
  | Some(_) => {name: "ready"}
  | None => let result = await get(); result == "yes" ? {name: "done"} : {name: "pending"}
  }
}
