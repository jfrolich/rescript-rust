type hidden
type visible = array<hidden>
let visible_encode: visible => JSON.t
let visible_decode: JSON.t => Spice.result<visible>
