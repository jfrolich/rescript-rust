let either = (hidden, first, fallback, second, fallback2, test) => {
  let enabled = if hidden {
    false
  } else {
    switch first {
    | Some(value) if test(value) => true
    | _ => fallback->Option.map(test)->Option.getOr(false)
    } ||
    switch second {
    | Some(value) if test(value) => true
    | _ => fallback2->Option.map(test)->Option.getOr(false)
    }
  }
  (enabled, hidden)
}

let both = (hidden, first, fallback, second, fallback2, test) => {
  let enabled = if hidden {
    false
  } else {
    switch first {
    | Some(value) if test(value) => true
    | _ => fallback->Option.map(test)->Option.getOr(false)
    } &&
    switch second {
    | Some(value) if test(value) => true
    | _ => fallback2->Option.map(test)->Option.getOr(false)
    }
  }
  (enabled, hidden)
}
