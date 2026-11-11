// `Done | Failed` are two plain objects. The compiler tells them apart by a
// field only one of them has: `"result" in outcome`.
module Jobs = %ts("./jobs.ts")

let message = job =>
  switch Jobs.run(job) {
  | Done({result}) => result
  | Failed({error, ?code}) =>
    switch code {
    | Some(code) => `${error} (${Float.toString(code)})`
    | None => error
    }
  }

// Both have `value`, of another kind in each:
// `typeof cell.value === "number"`.
let text = (cell: Jobs.showCell) =>
  switch cell {
  | Amount({value}) => Float.toFixed(value, ~digits=2)
  | Label({value}) => value
  }

// A case is the plain object itself.
let shown = Jobs.show(Amount({value: 3.}))
