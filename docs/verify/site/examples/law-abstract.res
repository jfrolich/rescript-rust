module Email: {
  type t
  let make: string => option<t>
  let toString: t => string
} = {
  type t = string
  let make = text => String.includes(text, "@") ? Some(text) : None
  let toString = email => email
}

@law
let roundTrip = (email: Email.t) => Email.make(Email.toString(email)) == Some(email)
