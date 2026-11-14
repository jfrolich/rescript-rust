// Identity codecs compose with record, container and variant plans.
@spice type value = JSON.t
@spice type values = array<JSON.t>
@spice type record = {value: JSON.t, optional?: JSON.t, values: option<array<JSON.t>>}
@spice type variant = Empty | Value(JSON.t) | Values(array<JSON.t>)

// Legacy spelling: the runtime no longer supplies the Js namespace.
module Js = {module Json = JSON}
@spice type optional = option<JSON.t>
@spice type linked = list<JSON.t>
@spice type dictionary = dict<JSON.t>
@spice type nested = array<option<JSON.t>>
@spice type tuple = (JSON.t, int)
@spice type outcome = result<JSON.t, string>
@spice type legacyArray = array<Js.Json.t>
@spice type legacyOption = option<Js.Json.t>
@spice type legacyList = list<Js.Json.t>
@spice type legacyDict = dict<Js.Json.t>
@spice type nestedOption = option<option<JSON.t>>
@spice type optionalArray = option<array<JSON.t>>
@spice type nullValue = Null.t<JSON.t>
@spice.decode type decodedArray = array<JSON.t>
@spice.decode type decodedNested = array<option<JSON.t>>

// A local identity alias is resolved through its generated codec value.
@spice type j = JSON.t
@spice type viaAlias = array<j>
@spice type viaAliasOption = option<array<j>>
@spice type aliasRecord = {items: array<j>}
@spice type nestedDictionary = dict<option<JSON.t>>
@spice type optionalList = option<list<JSON.t>>
@spice type viaAliasIdentity = j
@spice type viaAliasSingleOption = option<j>
module AliasNested = {
  @spice type nestedAliasArray = array<j>
}
