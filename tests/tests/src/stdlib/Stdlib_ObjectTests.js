let eq = (a, b) => %equal()(b, a);

Test.run(true, eq, Object.is()(25, 25), %loc_POS()("is: ints"));

Test.run(true, eq, Object.is()("abc", "abc"), %loc_POS()("is: strings"));

Test.run(false, eq, Object.is()("ABC", "abc"), %loc_POS()("is: strings"));

Test.run(false, eq, Object.is()(undefined, undefined), %loc_POS()("is: null and undefined"));

Test.run(true, eq, Object.is()(undefined, undefined), %loc_POS()("is: null and undefined"));

Test.run(true, eq, Object.is()(undefined, undefined), %loc_POS()("is: null and undefined"));

let nums = [1, 2, 3];

Test.run(false, eq, Object.is()([1, 2, 3], [1, 2, 3]), %loc_POS()("is: arrays"));

Test.run(true, eq, Object.is()(nums, nums), %loc_POS()("is: arrays"));

Test.run(true, eq, %equal()([1, 2, 3], [1, 2, 3]), %loc_POS()("is: arrays"));

Test.run(false, eq, [1, 2, 3] === [1, 2, 3], %loc_POS()("is: arrays"));

Test.run(false, eq, Object.is()({TAG: "::", _0: 1, _1: {TAG: "::", _0: 2, _1: {TAG: "::", _0: 3, _1: "[]"}}}, {TAG: "::", _0: 1, _1: {TAG: "::", _0: 2, _1: {TAG: "::", _0: 3, _1: "[]"}}}), %loc_POS()("is: list"));

Test.run(true, eq, %equal()({TAG: "::", _0: 1, _1: {TAG: "::", _0: 2, _1: {TAG: "::", _0: 3, _1: "[]"}}}, {TAG: "::", _0: 1, _1: {TAG: "::", _0: 2, _1: {TAG: "::", _0: 3, _1: "[]"}}}), %loc_POS()("is: list"));

Test.run(false, eq, {TAG: "::", _0: 1, _1: {TAG: "::", _0: 2, _1: {TAG: "::", _0: 3, _1: "[]"}}} === {TAG: "::", _0: 1, _1: {TAG: "::", _0: 2, _1: {TAG: "::", _0: 3, _1: "[]"}}}, %loc_POS()("is: list"));

let d = Date()(1, 2000);

Test.run(false, eq, Object.is()(Date()(1, 2000), Date()(1, 2000)), %loc_POS()("is: date"));

Test.run(true, eq, Object.is()(d, d), %loc_POS()("is: date"));

let x = ()(1);

Test.run(true, eq, Object.is()(x, x), %loc_POS()("is: objects"));

Test.run(false, eq, Object.is()(()(1), ()(1)), %loc_POS()("is: objects"));

Test.run(false, eq, Object.is()(()("()"), ()("()")), %loc_POS()("is: objects"));

Test.run(true, eq, x === x, %loc_POS()("is: === and == operator"));

Test.run(true, eq, %equal()(x, x), %loc_POS()("is: === and == operator"));

Test.run(true, eq, %equal()(()(1), ()(1)), %loc_POS()("is: === and == operator"));

Test.run(true, eq, Object.is()(0, 0), %loc_POS()("is: zeros"));

Test.run(true, eq, Object.is()(-0.0, -0.0), %loc_POS()("is: zeros"));

Test.run(false, eq, Object.is()(-0.0, 0.0), %loc_POS()("is: zeros"));

let mkBig = s => Stdlib.BigInt.fromString(s);

Test.run(true, eq, Object.is()(mkBig("123456789"), mkBig("123456789")), %loc_POS()("is: bigint"));

Test.run(false, eq, Object.is()(mkBig("123456789"), mkBig("123489")), %loc_POS()("is: bigint"));

Test.run(true, eq, Object.is()(mkBig("0"), mkBig("000000000")), %loc_POS()("is: bigint"));

Test.run(true, eq, %equal()(mkBig("123"), mkBig("123")), %loc_POS()("is: bigint"));

Test.run(true, eq, mkBig("123") === mkBig("123"), %loc_POS()("is: bigint"));

Test.run(()(0, 3, 1), eq, Object.assign()(()(0, 3), ()(2, 1)), %loc_POS()("assign copies from source to target"));

let assignOverwritesTarget = (title, source) => {
  let sourceObj = ()(source);
  Test.run(sourceObj, eq, Object.assign()(sourceObj, ()(1)), %loc_POS()("assign " + title + ""));
  Test.run(sourceObj, eq, Object.assign()(sourceObj, ()(undefined)), %loc_POS()("assign " + title + ""));
  return Test.run(sourceObj, eq, Object.assign()(sourceObj, ()(undefined)), %loc_POS()("assign " + title + ""));
};

assignOverwritesTarget(undefined, "when source is undefined");

assignOverwritesTarget(undefined, "when source is null");

assignOverwritesTarget(1, "when source is a number");

assignOverwritesTarget("abc", "when source is a string");

let runGetTest = i => Test.run(i.expected, eq, i.get(i.source("()")), %loc_POS()("Object.get: " + i.title + ""));

runGetTest({title: "prop exists, return Some", source: _arg0 => ()(1), get: __x => ()("a", __x), expected: {TAG: "Some", _0: 1}});

runGetTest({title: "prop NOT exist, return None", source: _arg0 => ()(1), get: i => ()("banana", i), expected: "None"});

runGetTest({title: "prop like toString, return Some", source: _arg0 => ()(1), get: i => Stdlib.Option.isSome(()("toString", i)), expected: true});

runGetTest({title: "prop exist but explicitly undefined, return None", source: _arg0 => ()(undefined), get: i => ()("a", i), expected: "None"});

runGetTest({title: "prop exist but explicitly null, return None", source: _arg0 => ()(undefined), get: i => ()("a", i), expected: {TAG: "Some", _0: undefined}});

runGetTest({title: "prop exists and is an array, can get it", source: _arg0 => ()([1, 2, 3]), get: i => Stdlib.Option.getOr([], Stdlib.Option.map(i => concat()([4, 5], i), ()("a", i))), expected: [1, 2, 3, 4, 5]});

let getSymbolTestWhenExists = _arg0 => {
  let obj = ()("()");
  let fruit = Symbol()("fruit");
  ()("banana", fruit, obj);
  let retrieved = ()(fruit, obj);
  return Test.run({TAG: "Some", _0: "banana"}, eq, retrieved, %loc_POS()("Object.getSymbol when exists return it as Some"));
};

getSymbolTestWhenExists("()");

Test.run("None", eq, ()(Symbol()("fruit"), ()("()")), %loc_POS()("Object.getSymbol when not exists return it as None"));

Test.run({TAG: "Some", _0: 1}, eq, ()("a", Object.create()(()(1))), %loc_POS()("Object.create clones properties"));

Test.run("None", eq, ()("b", Object.create()(()(1))), %loc_POS()("Object.create clones properties"));