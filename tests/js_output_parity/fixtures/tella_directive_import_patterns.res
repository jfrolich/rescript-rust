@@directive("'use client';")

type router

@module("react") external useState: (unit => 'state) => ('state, ('state => 'state) => unit) = "useState"
@module("react") external useMemo1: (unit => 'value, array<'dep>) => 'value = "useMemo"
@module("next/navigation") external useRouter: unit => router = "useRouter"
@send external push: (router, string) => unit = "push"

type copyState = Idle | Copied

let useClientState = (~initial="") => {
  let (state, setState) = useState(() => Idle)
  let (value, setValue) = useState(() => initial)

  let copy = next => {
    setState(_ => Copied)
    setValue(_ => next)
  }

  useMemo1(() => (state, value, copy), [value])
}

module NestedClient = {
  @@directive("'use client';")

  let navigate = (~segment, ()) => {
    let router = useRouter()
    let href = "/stories/" ++ segment
    router->push(href)
    href
  }
}

let output = (useClientState, NestedClient.navigate)
