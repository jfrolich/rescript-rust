module Custom = {
  type t = int
  let t_encode = (_: string) => JSON.Null
  let t_encodeJson = t_encode
  let t_decode = (_: JSON.t): result<t, Spice.decodeError> => Ok(0)
}
@spice
type t = {value: Custom.t}
