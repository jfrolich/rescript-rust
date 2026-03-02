let mapOfArray = x => M.fromArray(x);

let setOfArray = x => N.fromArray(x);

let emptyMap = _arg0 => M.empty;

describe()(_arg0 => test()(_arg0 => {
  let v = A.makeByAndShuffle(i => [i, i], 1000000);
  let u = M.fromArray(v);
  M.checkInvariantInternal(u);
  let firstHalf = A.slice(2000, 0, v);
  let xx = A.reduce((acc, _arg1) => M.remove(x, acc), u, firstHalf);
  M.checkInvariantInternal(u);
  return M.checkInvariantInternal(xx);
}, "bs map test"), %loc_MODULE());