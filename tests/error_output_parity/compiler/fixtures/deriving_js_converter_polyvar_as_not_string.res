// error-output-parity: jsConverter reads each polymorphic variant tag @as as a string
@deriving(jsConverter)
type orientation = [
  | @as() #Horizontal
  | #Vertical
]
