type rec tree =
  | Leaf(int)
  | Branch({left: tree, right: tree, label?: string})

type color =
  | Orange
  | Color(string)

type box = {
  hi: int,
  lo: list<option<int>>,
}

type auth = [
  | #Authenticated(int)
  | #Unauthenticated
  | #Unverified(int)
]

type route = [
  | #Dashboard
  | #Invite
  | #Onboarding(int)
  | #SignIn
]

exception Api({code: int, message: string})

let rec sumTree = tree =>
  switch tree {
  | Leaf(value) => value
  | Branch({left: Leaf(0), right: Leaf(value), label})
    if String.length(label) > 0 =>
    value + String.length(label)
  | Branch({left, right}) => sumTree(left) + sumTree(right)
  }

let matchList = values =>
  switch values {
  | list{a0, a1, a2, a3, a4, a5, ..._} => a0 + a1 + a2 + a3 + a4 + a5
  | list{single} => single
  | list{} => 0
  | _ => -1
  }

let matchArray = values =>
  switch values {
  | [a0, a1, a2, a3] => a0 + a1 + a2 + a3
  | [single] => single
  | [] => 0
  | _ => -1
  }

let matchRecord = value =>
  switch value {
  | {hi: 3, lo: list{None, None, Some(2), Some(1), Some(_), ..._}} => 2
  | {hi: 2, lo: list{None, Some(value), ..._}} => value
  | {hi, lo: list{Some(value), ..._}} if hi > value => hi - value
  | _ => 0
  }

let matchConstructorLiteral = color =>
  switch color {
  | Orange => "orange"
  | Color("#ffff") => "white"
  | Color(name) => name
  }

let matchTupleOr = (auth, route) =>
  switch (auth, route) {
  | (#Unauthenticated, #Onboarding(step))
  | (#Unverified(_), #Onboarding(step)) =>
    step
  | (#Unauthenticated, #SignIn) | (#Unauthenticated, #Invite) => 1
  | (#Authenticated(user), #Dashboard) => user
  | _ => 0
  }

let matchListAlias = values =>
  switch values {
  | list{(name, _) as head, ...tail} =>
    name ++ ":" ++ Int.toString(Pair.second(head) + List.length(tail))
  | list{} => "empty"
  }

let handleException = run =>
  try {
    run()
    "ok"
  } catch {
  | Api({code: 404, message}) => message
  | Api({code}) when code >= 500 => "server"
  | _ => "other"
  }

let allValues = (
  sumTree(Branch({left: Leaf(0), right: Leaf(3), label: "ok"})),
  matchList(list{1, 2, 3, 4, 5, 6, 7}),
  matchArray([1, 2, 3, 4]),
  matchRecord({hi: 3, lo: list{None, None, Some(2), Some(1), Some(5)}}),
  matchConstructorLiteral(Color("#ffff")),
  matchTupleOr(#Unverified(2), #Onboarding(4)),
  matchListAlias(list{("a", 1), ("b", 2)}),
  handleException(() => throw(Api({code: 404, message: "missing"}))),
)
