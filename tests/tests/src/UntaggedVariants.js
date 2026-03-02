let i = {TAG: "I", _0: 42};

let i2 = {TAG: "I2", _0: 42.5};

let s = {TAG: "S", _0: "abc"};

let s2 = {TAG: "S2", _0: "abc"};

let classify = x => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "I") {
    ifres = "An integer";
  } else {
    let ctor = x;
    let ifres;
    if (ctor.TAG === "S") {
      let s = ctor._0;
      ifres = "A string" + s;
    } else {
      ifres = x === "A" ? "A" : undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let classify2 = x => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "I2") {
    ifres = "A float";
  } else {
    let ctor = x;
    let ifres;
    if (ctor.TAG === "S2") {
      let s = ctor._0;
      ifres = "A string" + s;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let w = {TAG: "Object", _0: {x: 10, y: ""}};

let cls = x => {
  let ifres;
  if (x === "One") {
    ifres = "one";
  } else {
    let ifres;
    if (x === "Two") {
      ifres = "two";
    } else {
      let ctor = x;
      let ifres;
      if (ctor.TAG === "Object") {
        let record = ctor._0;
        let y = record.y;
        ifres = "object" + y;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let tuplesToObjects;

tuplesToObjects = _arg0 => {
  let ifres;
  if (l === "Empty") {
    ifres = "Empty";
  } else {
    let ctor = l;
    let ifres;
    if (ctor.TAG === "Cons") {
      let tuple = ctor._0;
      let hd = tuple[0];
      let tl = tuple[1];
      ifres = {TAG: "Cons", _0: {hd: hd, tl: tuplesToObjects(tl)}};
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let l1 = {TAG: "Cons", _0: [1, {TAG: "Cons", _0: [2, {TAG: "Cons", _0: [3, "Empty"]}]}]};

let l2 = tuplesToObjects(l1);

console.log()(l1, "l1");

console.log()(l2, "l2");