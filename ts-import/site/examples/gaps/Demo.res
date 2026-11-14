// Each of these imports compiles, with a type that says less than the
// TypeScript one. "TypeScript" on the right lists what was lost.
let {parse, resolve, log, byId, debounce} = %ts("./loose.ts")

// Only the first signature of `parse` is imported.
let n = parse("42")

// `any` as an argument is a type variable: anything is accepted.
log("ready", [1, 2, 3])

// The constraint `T extends {id: string}` is not checked here.
let found = byId([{"id": "a"}], "a")

debounce(() => Console.log("later"))
