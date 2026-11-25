// A literal alias selects scalar JSON, but the general decoder still tries
// to read the payload from json_arr, which that form never binds.
@spice
type t = @spice.as("A") A(int)
