// A library whose codecs are typed through abbreviations and whose option
// combinators are curried. The types recorded for the derived codecs below
// come from these signatures, whichever way the derive is compiled.
module Spice = {
  type json = JSON.t
  type encoder<'a> = 'a => json
  type decoded<'a> = result<'a, Spice.decodeError>
  type decoder<'a> = json => decoded<'a>

  let stringToJson: encoder<string> = Spice.stringToJson
  let stringFromJson: decoder<string> = Spice.stringFromJson

  let arrayToJson: (encoder<'a>, array<'a>) => json = Spice.arrayToJson
  let arrayFromJson: (decoder<'a>, json) => decoded<array<'a>> = Spice.arrayFromJson

  let optionToJson = encoder => opt => Spice.optionToJson(encoder, opt)
  let optionToNullableJson = encoder => opt => Spice.optionToNullableJson(encoder, opt)

  let optionFromJson: decoder<'a> => decoder<option<'a>> = decoder =>
    json => Spice.optionFromJson(decoder, json)
}

@spice
type name = string

@spice
type names = array<name>

@spice
type maybeName = option<name>

@spice
type nested = array<option<names>>

let roundTrip = (value: nested) => nested_decode(nested_encode(value))
