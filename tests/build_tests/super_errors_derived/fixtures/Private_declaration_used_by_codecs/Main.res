// The interface keeps the types abstract; the generated codecs use every
// label and constructor, so none is reported unused.
@spice
type shape = Circle(int) | Square

@spice
type point = {x: int, shape: shape}
