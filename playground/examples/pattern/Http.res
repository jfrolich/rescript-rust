open Macro

// A macro that returns `pat` is used where a pattern is written.
@macro
let status = (name: string): pat =>
  switch name {
  | "ok" => %pat(200 | 201 | 204)
  | "redirect" => %pat(301 | 302 | 307 | 308)
  | "missing" => Pat.int(404)
  | "server error" => %pat(500 | 502 | 503)
  | _ => error(`Http.status: "${name}" is not a status this macro knows`)
  }

// A literal that is checked and converted while compiling.
@macro
let color = (hex: string): code<(int, int, int)> => {
  let channel = (start: int) => {
    let value = Float.parseInt(String.slice(hex, ~start, ~end=start + 2), ~radix=16)
    Float.isNaN(value) ? error(`Http.color: "${hex}" is not a color like #ff8800`) : Code.int(Float.toInt(value))
  }
  if String.length(hex) != 7 || !String.startsWith(hex, "#") {
    error(`Http.color: "${hex}" is not a color like #ff8800`)
  } else {
    Code.tuple([channel(1), channel(3), channel(5)])
  }
}
