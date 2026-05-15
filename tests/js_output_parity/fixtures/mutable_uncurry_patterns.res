let eqRef = (left, {contents: right}) => left.contents == right

let tuple3 = ({contents: first}, {contents: second}, {contents: third}) => (
  first,
  second,
  third,
)

let tuple4 = (
  {contents: first},
  {contents: second},
  {contents: third},
  {contents: fourth},
) => (first, second, third, fourth)

let tuple5 = (
  {contents: first},
  {contents: second},
  {contents: third},
  {contents: fourth},
  {contents: fifth},
) => (first, second, third, fourth, fifth)

let nestedTuple = ({contents: first}, {contents: second}, {contents: third}) => {
  let base = first + second + third
  ({contents: nextFirst}, {contents: nextSecond}, {contents: nextThird}) =>
    base + nextFirst + nextSecond + nextThird
}

let shadowedParamNames = ({contents: eqRef}, {contents: tuple3}, {contents: tuple4}) => (
  eqRef,
  tuple3,
  tuple4,
)

let allValues = (
  eqRef(ref(1), ref(2)),
  eqRef(ref(2), ref(2)),
  tuple3(ref(1), ref(2), ref(3)),
  tuple4(ref(1), ref(2), ref(3), ref(4)),
  tuple5(ref(1), ref(2), ref(3), ref(4), ref(5)),
  nestedTuple(ref(1), ref(2), ref(3))(ref(4), ref(5), ref(6)),
  shadowedParamNames(ref(7), ref(8), ref(9)),
)
