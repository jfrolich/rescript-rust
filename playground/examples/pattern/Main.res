let describe = (code: int) =>
  switch code {
  | %Http.status("ok") => "fine"
  | %Http.status("redirect") => "moved"
  | %Http.status("missing") => "not found"
  | %Http.status("server error") => "broken"
  | _ => "something else"
  }

Console.log([200, 302, 404, 503, 418]->Array.map(describe))

let (red, green, blue) = %Http.color("#ff8800")
Console.log3(red, green, blue)

// Not a color, so not a program:
// let oops = %Http.color("#ff88")
