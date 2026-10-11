type rec t<'a> = A('a): t<'a> | B('a): t<'a>
let f = (x: t<[#a]>) => (x :> t<[#a | #b]>)
let r = ref(None)
let g = () => A([])
let h = g()
let k: t<array<int>> = h
let k2: t<array<string>> = h
