type classification = NotFound | BadRequest(string) | ServerError(string) | RateLimited

type source
@get external getCode: source => Nullable.t<int> = "code"
@val external reportError: (string, option<int>, option<int>, option<int>, option<int>, string) => unit = "reportError"

let classify = (source, clientMessage, serverMessage) =>
  switch source->getCode->Nullable.toOption {
  | None =>
    reportError(serverMessage, None, None, None, None, serverMessage)
    ServerError(serverMessage)
  | Some(401 | 403) =>
    reportError(serverMessage, None, None, None, None, serverMessage)
    ServerError(serverMessage)
  | Some(404) => NotFound
  | Some(429) => RateLimited
  | Some(value) if value >= 400 && value < 500 => BadRequest(clientMessage)
  | _ =>
    reportError(serverMessage, None, None, None, None, serverMessage)
    ServerError(serverMessage)
  }
