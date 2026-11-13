// Identity codecs compose with record, container and variant plans.
@spice type value = JSON.t
@spice type values = array<JSON.t>
@spice type record = {value: JSON.t, optional?: JSON.t, values: option<array<JSON.t>>}
@spice type variant = Empty | Value(JSON.t) | Values(array<JSON.t>)
