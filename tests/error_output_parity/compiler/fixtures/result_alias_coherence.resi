type t<'ok, 'error> = result<'ok, 'error> =
  | Ok('ok)
  | Error('error)
