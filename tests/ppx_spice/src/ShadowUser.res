@spice type j = int
module Opened = {
  open AliasOwner
  @spice type viaShadowingOpen = array<j>
}
module Included = {
  include AliasOwner
  @spice type viaInclude = array<j>
}
// A local expression open can enclose a module containing derived declarations.
let localCodec = {
  open AliasOwner
  module Local = {
    @spice type viaExpressionOpen = array<j>
  }
  Local.viaExpressionOpen_encodeJson
}
