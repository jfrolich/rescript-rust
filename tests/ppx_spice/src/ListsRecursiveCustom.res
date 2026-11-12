@spice
type ints = list<int>

@spice
type rec tree = Leaf(int) | Branch(list<tree>)

@spice
type rec left = Left(option<right>)
@spice
and right = Right(option<left>)

module Custom: {
  type t
  let t_encode: t => JSON.t
  let t_encodeJson: t => JSON.t
  let t_decode: JSON.t => result<t, Spice.decodeError>
} = {
  type t = int
  let t_encode = Spice.intToJson
  let t_encodeJson = Spice.intToJson
  let t_decode = Spice.intFromJson
}

@spice
type customRecord = {value: Custom.t}
