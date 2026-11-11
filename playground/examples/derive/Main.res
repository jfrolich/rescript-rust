@Enum.derive
type color =
  | Red
  | Green
  | @Enum.label("navy blue") Blue

Console.log(colorValues->Array.map(colorToString))
Console.log(colorFromString("navy blue") == Some(Blue))
Console.log(colorFromString("purple"))
