module Legacy = {
  type completion = result<int, string> => unit
  type dup = {completion: option<completion>, id: string}
  type t = DuplicateScene(dup) | Other
}
type outbound = Legacy(Legacy.t) | Wire
