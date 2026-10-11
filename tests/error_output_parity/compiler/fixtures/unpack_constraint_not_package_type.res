let extract = m => {
  module M = unpack(m: [#a | #b])
  M
}
