@partial
type config = {
  host: string,
  port: int,
  debug: bool,
}

// Use the generated config_partial type
let partial: config_partial = {
  host: "localhost",
}
