let eq = (a, b) => %equal()(b, a);

let iterator = ();

let syncResult = %makeref()("None");

forEach()(v => %equal()("b", v) ? (syncResult.contents = {TAG: "Some", _0: "b"}, undefined) : undefined, iterator);

Test.run({TAG: "Some", _0: "b"}, eq, syncResult.contents, %loc_POS()("Sync forEach"));

let asyncIterator = ();

let asyncResult = %makeref()("None");

await Stdlib.AsyncIterator.forEach(v => {
  let ctor = v;
  let ifres;
  if (ctor.TAG === "Some") {
    let tuple = ctor._0;
    let ifres;
    if (tuple[0] === "second") {
      let _value = tuple[1];
      ifres = (asyncResult.contents = {TAG: "Some", _0: "second"}, undefined);
    } else {
      ifres = "()";
    }
    ifres = ifres;
  } else {
    ifres = "()";
  }
  return ifres;
}, asyncIterator);

Test.run({TAG: "Some", _0: "second"}, eq, asyncResult.contents, %loc_POS()("Async forEach"));

let asyncIterator = Stdlib.AsyncIterator.make(_arg0 => {
  let currentCount = local_1.count.contents;
  %refset()(%add()(1, currentCount), local_1.count);
  let call = (prim => prim)(currentCount === 3 ? Stdlib.AsyncIterator.done({TAG: "Some", _0: currentCount}) : Stdlib.AsyncIterator.value(currentCount));
  return call;
});

await Stdlib.AsyncIterator.forEach(v => {
  let ctor = v;
  return ctor.TAG === "Some" ? (ctor._0 === 3 ? (local_1.asyncResult.contents = {TAG: "Some", _0: "done"}, undefined) : console.log()("next..")) : console.log()("next..");
}, asyncIterator);

Test.run({TAG: "Some", _0: "done"}, eq, local_1.asyncResult.contents, %loc_POS()("Creating your own async iterator"));