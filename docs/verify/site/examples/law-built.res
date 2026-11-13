module Email: {
  type t
  let make: string => option<t>
  let toString: t => string
} = {
  type t = string
  let make = text => String.includes(text, "@") ? Some(text) : None
  let toString = email => email
}

// Every email the program can have was made by Email.make.
@law
let roundTrip = (text: string) =>
  switch Email.make(text) {
  | Some(email) => Email.toString(email) == text
  | None => !String.includes(text, "@")
  }

let clamp = (x, low, high) => x < low ? low : x > high ? high : x

// A law with a condition: it says nothing when low is above high.
@law
let clampStaysInRange = (x: int, low: int, high: int) =>
  low > high || {
      let clamped = clamp(x, low, high)
      low <= clamped && clamped <= high
    }
