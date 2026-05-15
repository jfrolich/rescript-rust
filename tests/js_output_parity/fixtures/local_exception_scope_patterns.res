exception Shared(int)

type payload = {
  code: int,
  label?: string,
}

let localSearch = (values: array<int>) => {
  exception Found(int);

  try {
    for index in 0 to values->Array.length - 1 {
      let value = values->Array.getUnsafe(index)
      if value > 3 {
        throw(Found(value))
      }
    }
    0
  } catch {
  | Found(value) => value
  | _ => -1
  }
}

let nestedShadow = value => {
  exception Stop(int);

  let numeric =
    try {
      if value > 0 {
        throw(Stop(value))
      }
      0
    } catch {
    | Stop(found) => found
    | _ => -1
    }

  let textual = {
    exception Stop(string);

    try {
      if value == 0 {
        throw(Stop("zero"))
      }
      "ok"
    } catch {
    | Stop(found) => found
    | _ => "other"
    }
  }

  (numeric, textual)
}

let recordPayload = maybeLabel => {
  exception Halt(payload);

  try {
    switch maybeLabel {
    | Some(label) => throw(Halt({code: String.length(label), label}))
    | None => throw(Halt({code: 0}))
    }
  } catch {
  | Halt({code, label}) => code + String.length(label)
  | Halt({code}) => code
  | _ => -1
  }
}

let exceptionSwitch = run =>
  switch run() {
  | exception Shared(value) => value
  | value => value
  }

let allValues = (
  localSearch([1, 2, 5, 8]),
  nestedShadow(3),
  nestedShadow(0),
  recordPayload(Some("abc")),
  recordPayload(None),
  exceptionSwitch(() => throw(Shared(7))),
  exceptionSwitch(() => 9),
)
