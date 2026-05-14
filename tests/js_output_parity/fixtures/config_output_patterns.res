@@config(no_export)

type retained = {
  count: int,
}

let retained = {count: 1}

let localFn = value => value + retained.count

module Local = {
  let value = "local"
}

let () = Js.log2(Local.value, localFn(2))
