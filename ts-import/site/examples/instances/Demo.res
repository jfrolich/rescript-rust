// A class that the module exports is a record with a class: the compiler
// knows to recognize its instances with `instanceof`.
module Garage = %ts("./garage.ts")

// So a union of classes is a variant, and can be matched on. `Car`
// extends `Vehicle`, and is tested first.
let describe = (what: Garage.parkWhat) =>
  switch what {
  | String(plate) => `the car with plate ${plate}`
  | Car(car) => `${car.plate} goes ${car.honk()}`
  | Vehicle(vehicle) => `something on ${Float.toString(vehicle.wheels)} wheels`
  }

let car = Garage.Car.make("RS-13")
let spot = Garage.park(Car(car))

// A subclass is its superclass too.
let wheels = (car :> Garage.vehicle).wheels

// `string | symbol`, and global classes such as `URL` and `Date`.
let isNamed = (event: Garage.listenEvent) =>
  switch event {
  | String(_) => true
  | Symbol(_) => false
  }
