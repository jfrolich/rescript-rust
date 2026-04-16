type user = {
  name: string,
  age: int,
}

@comptime
let encode = (comptime T: type, value: T): Js.Json.t => {
  switch @typeInfo(T) {
  | String => Js.Json.string(value)
  | Int => Js.Json.number(Int.toFloat(value))
  | Record({fields}) =>
    let obj = Js.Dict.empty()
    inline for field in fields {
      Js.Dict.set(obj, field.name, encode(field.typ, @field(value, field.name)))
    }
    Js.Json.object_(obj)
  | _ => @compileError(`Cannot encode`)
  }
}

let myUser: user = {name: "Alice", age: 30}
let json = encode(user, myUser)
