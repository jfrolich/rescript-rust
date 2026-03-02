let empty = IntMap.empty;

let m = Belt.List.reduceReverse((acc, _arg1) => IntMap.set(v, k, acc), empty, {TAG: "::", _0: [10, /* a */97], _1: {TAG: "::", _0: [3, /* b */98], _1: {TAG: "::", _0: [7, /* c */99], _1: {TAG: "::", _0: [20, /* d */100], _1: "[]"}}}});

let s = Belt.List.reduceReverse((acc, _arg1) => SMap.set(v, k, acc), SMap.empty, {TAG: "::", _0: ["10", /* a */97], _1: {TAG: "::", _0: ["3", /* b */98], _1: {TAG: "::", _0: ["7", /* c */99], _1: {TAG: "::", _0: ["20", /* d */100], _1: "[]"}}}});

describe()(_arg0 => {
  test()(_arg0 => Test_utils.eq({TAG: "Some", _0: /* a */97}, IntMap.get(10, m), %loc_LOC()), "int");
  return test()(_arg0 => Test_utils.eq({TAG: "Some", _0: /* a */97}, SMap.get("10", s), %loc_LOC()), "string");
}, %loc_MODULE());