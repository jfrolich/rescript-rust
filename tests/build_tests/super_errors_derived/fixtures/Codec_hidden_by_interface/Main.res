// The interface hides every codec of `hidden`: no unused-value warning.
@spice
type hidden = string

@spice
type visible = array<hidden>
