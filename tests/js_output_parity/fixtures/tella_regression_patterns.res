// Shapes minimized from the external corpus.

// An exported alias of a string binding stays an alias (lam_coercion.ml:82-172).
let storageFullHelpSlug = "troubleshooting/not-enough-storage-to-record"
let insufficientStorageHelpSlug = storageFullHelpSlug

// @as payloads are already JS-escaped source text (E.tag_type, DStarJ).
type key = | @as("\\") Backslash | @as("\"") Quote | Plain
let keys = [Backslash, Quote, Plain]

// A record update of an inlined object literal is a parenthesized spread.
type word = {confidence: float, start: float, text: string, alignedStart?: float}
let word = (start, text): word => {confidence: 0.98, start, text}
let words = [{...word(1000., "Original"), alignedStart: 1.}]

// Early returns stay sibling guards (js_dump.ml function_body).
type pos = Trim(int) | Stretch
type kind = Mask | Other
type layer = {id: string, type_: kind, position: option<pos>}
type section = {id: string, layoutName: string}
let pick = (section: option<section>, layer: option<layer>) =>
  switch (section, layer) {
  | (_, Some({type_: Mask})) => None
  | (_, Some({position: Some(Trim(_))})) => None
  | (Some({layoutName: "custom"}), Some({position: Some(Stretch)})) => {
      Console.log("x")
      None
    }
  | (Some(_), Some(layer)) => Some(layer)
  | _ => None
  }

// An untagged switch with a no-op constant case keeps its dispatch test.
type ev = {x: int}
@unboxed
type dragStart =
  | @as(false) NoDragStart
  | DragStart(ev)
type resizeStart = {dragStart: dragStart}
@send external setTranslate: (ev, int) => unit = "set"
let onResizeStart = (e: resizeStart) => {
  switch e.dragStart {
  | DragStart(start) => start->setTranslate(1)
  | NoDragStart => ()
  }
  Console.log("dragging")
}

// A Some around a local abbreviation of a variant needs no nesting check.
module SupportType = {
  type t = Bug | Feedback
}
module Config = {
  type t = SupportType.t
}
type state = {initialType: Config.t}
type props<'a> = {initialSupportType?: 'a}
let makeProps = (state: state) => ({initialSupportType: state.initialType}: props<_>)

// Identical exit handlers share one switch clause (group_apply).
module Log = {
  let error = (~call: string, ~err=?, ~error: string, ~extra=?, ~more=?, key: string) => {
    ignore((call, err, error, extra, more, key))
    Console.log(key)
  }
}
type apiError = NotFound | ServerError(string) | RateLimited | BadRequest(string)
let classify = (~call, ~logKey, ~clientMessage, ~serverMessage, code: option<int>, message) =>
  switch code {
  | Some(404) => NotFound
  | Some(401) | Some(403) =>
    Log.error(~call, ~error=message, logKey)
    ServerError(serverMessage)
  | Some(429) =>
    Log.error(~call, ~error=message, logKey)
    RateLimited
  | Some(code) if code >= 400 && code < 500 => BadRequest(clientMessage)
  | _ =>
    Log.error(~call, ~error=message, logKey)
    ServerError(serverMessage)
  }

// A multi-line index expression is indented by Array_index's two groups.
let peak = (data: array<float>, i, top) => {
  let v = data[2 * i + (top ? 1 : 0)]->Option.getOr(0.)
  top ? Math.max(0., v) : Math.max(0., -.v)
}
