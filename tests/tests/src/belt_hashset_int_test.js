let add = (x, y) => %add()(y, x);

let sum2 = h => {
  let v = %makeref()(0);
  N.forEach(x => %refset()(%add()(x, v.contents), v), h);
  return v.contents;
};

describe()(_arg0 => {
  test()(_arg0 => {
    let u = A.concat(I.randomRange(120, 40), I.randomRange(100, 30));
    let v = N.fromArray(u);
    Test_utils.eq(91, N.size(v), %loc_LOC());
    let xs = S.toArray(S.fromArray(N.toArray(v)));
    Test_utils.eq(I.range(120, 30), xs, %loc_LOC());
    let x = %mul()(91, %div()(2, %add()(120, 30)));
    Test_utils.eq(x, N.reduce(add, 0, v), %loc_LOC());
    return Test_utils.eq(x, sum2(v), %loc_LOC());
  }, "fromArray");
  test()(_arg0 => {
    let u = A.concat(I.randomRange(100, 0), I.randomRange(100000, 0));
    let v = N.make(40);
    N.mergeMany(u, v);
    Test_utils.eq(100001, N.size(v), %loc_LOC());
    for (let i = 0; i <= 1000; ++i) {
      N.remove(i, v);
    }
    Test_utils.eq(99000, N.size(v), %loc_LOC());
    for (let i = 0; i <= 2000; ++i) {
      N.remove(i, v);
    }
    return Test_utils.eq(98000, N.size(v), %loc_LOC());
  }, "mergeMany");
  test()(_arg0 => {
    let u0 = N.fromArray(I.randomRange(100000, 0));
    let u1 = N.copy(u0);
    Test_utils.eq(N.toArray(u1), N.toArray(u0), %loc_LOC());
    for (let i = 0; i <= 2000; ++i) {
      N.remove(i, u1);
    }
    for (let i = 0; i <= 1000; ++i) {
      N.remove(i, u0);
    }
    let v0 = A.concat(N.toArray(u0), I.range(1000, 0));
    let v1 = A.concat(N.toArray(u1), I.range(2000, 0));
    SI.stableSortInPlace(v0);
    SI.stableSortInPlace(v1);
    return Test_utils.eq(v1, v0, %loc_LOC());
  }, "stableSortInPlace");
  return test()(_arg0 => {
    let h = N.fromArray(I.randomRange(1000000, 0));
    let histo = N.getBucketHistogram(h);
    return Test_utils.ok(%lessequal()(10, histo.length), %loc_LOC());
  }, "getBucketHistogram");
}, %loc_MODULE());