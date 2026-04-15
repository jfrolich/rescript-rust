type config = {
  name: string,
  debug: option<bool>,
}

let c: config = {
  name: "app",
  debug: Some(true),
}

let isDebug = switch c.debug {
| Some(v) => v
| None => false
}
