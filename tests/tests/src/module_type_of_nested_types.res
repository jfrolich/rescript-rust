module WritableStream = {
  type t
  type chunk = {data: int}
  type sink = {write: chunk => unit}
  @new external make: sink => t = "WritableStream"
}
let version = 1
