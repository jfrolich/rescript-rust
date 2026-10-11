module Structured = {
  module Combi = {
    module Landscape = {
      type cameraBubbleScreenStyle = Regular | Wide
      type t = CameraBubble({cameraSize: int, screenStyle: cameraBubbleScreenStyle})
      let toName = (x: t) =>
        switch x {
        | CameraBubble({cameraSize}) => Int.toString(cameraSize)
        }
    }
  }
}
