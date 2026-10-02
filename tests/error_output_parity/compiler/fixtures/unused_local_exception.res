@@warning("A")
let f = () => {
  exception E
  exception F
  try throw(E) catch {
  | E => 1
  }
}
