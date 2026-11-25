@spice type viaOther = array<AliasOwner.j>
@spice type viaOtherOption = option<array<AliasOwner.j>>
module Local = AliasOwner
@spice type viaModuleAlias = array<Local.j>
module Opened = {
  open AliasOwner
  @spice type viaOpen = array<j>
}
@spice type viaLegacy = array<AliasOwner.legacy>
@spice type viaRecordOwner = array<Records.t>
