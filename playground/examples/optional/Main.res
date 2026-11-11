type user = {
  name: string,
  age: int,
  nickname?: string,
}

// {name?: string, age?: int, nickname?: string}
type userPatch = %Patch.t(user)

let update = (user: user, patch: userPatch): user => Patch.apply(user, patch)

let ada: user = {name: "Ada", age: 36}

Console.log(ada->update({age: 37}))
Console.log(ada->update({nickname: "countess"}))
Console.log(ada->update({nickname: "countess"})->update({name: "Ada Lovelace"}))
