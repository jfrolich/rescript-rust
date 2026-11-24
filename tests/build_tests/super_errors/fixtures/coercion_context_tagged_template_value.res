let tag = TaggedTemplate.make((_: array<string>, _: array<string>) => "")
let f = (o: int) => tag`a${(o :> int)}`
