type address = {
  street: string,
  city: string,
}

type user = {
  name: string,
  address: address,
}

let u: user = {
  name: "Alice",
  address: {
    street: "123 Main St",
    city: "Springfield",
  },
}

let street = u.address.street
