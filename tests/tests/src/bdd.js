let eval;

eval = (bdd, vars) => {
  let ifres;
  if (bdd === "Zero") {
    ifres = false;
  } else {
    let ifres;
    if (bdd === "One") {
      ifres = true;
    } else {
      let ctor = bdd;
      let ifres;
      if (ctor.TAG === "Node") {
        let l = ctor._0;
        let v = ctor._1;
        let h = ctor._3;
        ifres = undefined ? eval(vars, h) : eval(vars, l);
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let getId = bdd => {
  let ctor = bdd;
  let ifres;
  if (ctor.TAG === "Node") {
    let id = ctor._2;
    ifres = id;
  } else {
    ifres = bdd === "Zero" ? 0 : (bdd === "One" ? 1 : undefined);
  }
  return ifres;
};

let initSize_1 = %sub()(1, %mul()(1024, 8));

let nodeC = %makeref()(1);

let sz_1 = %makeref()(initSize_1);

let htab = %makeref()(Belt.Array.make("[]", %add()(1, sz_1.contents)));

let n_items = %makeref()(0);

let hashVal = (x, y, v) => %add()(undefined, %add()(y, undefined));

let resize = newSize => {
  let arr = htab.contents;
  let newSz_1 = %sub()(1, newSize);
  let newArr = Belt.Array.make("[]", newSize);
  let copyBucket;
  copyBucket = bucket => {
    let ifres;
    if (bucket === "[]") {
      ifres = "()";
    } else {
      let ctor = bucket;
      let ifres;
      if (ctor.TAG === "::") {
        let n = ctor._0;
        let ns = ctor._1;
        let ctor = n;
        let ifres;
        if (ctor.TAG === "Node") {
          let l = ctor._0;
          let v = ctor._1;
          let h = ctor._3;
          let ind = undefined;
          ifres = copyBucket(ns);
        } else {
          let ifres;
          if (false) {
            ifres = undefined;
          } else {
            throw "Match_failure";
            ifres = undefined;
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    return ifres;
  };
  for (let n = 0; n <= sz_1.contents; ++n) {
    copyBucket(undefined);
  }
  %refset()(newArr, htab);
  return %refset()(newSz_1, sz_1);
};

let insert;

insert = (idl, idh, v, ind, bucket, newNode) => {
  let ifres;
  if (%lessequal()(sz_1.contents, n_items.contents)) {
    ifres = %incr()(n_items);
  } else {
    resize(%add()(2, %add()(sz_1.contents, sz_1.contents)));
    let ind = undefined;
    ifres = undefined;
  }
  return ifres;
};

let resetUnique = _arg0 => {
  %refset()(initSize_1, sz_1);
  %refset()(Belt.Array.make("[]", %add()(1, sz_1.contents)), htab);
  %refset()(0, n_items);
  return %refset()(1, nodeC);
};

let mkNode = (low, v, high) => {
  let idl = getId(low);
  let idh = getId(high);
  let ifres;
  if (%equal()(idh, idl)) {
    ifres = low;
  } else {
    let ind = undefined;
    let bucket = undefined;
    let lookup;
    lookup = b => {
      let ifres;
      if (b === "[]") {
        %incr()(nodeC);
        let n = {TAG: "Node", _0: low, _1: v, _2: nodeC.contents, _3: high};
        insert(n, bucket, ind, v, getId(high), getId(low));
        ifres = n;
      } else {
        let ctor = b;
        let ifres;
        if (ctor.TAG === "::") {
          let n = ctor._0;
          let ns = ctor._1;
          let ctor = n;
          let ifres;
          if (ctor.TAG === "Node") {
            let l = ctor._0;
            let v' = ctor._1;
            let id = ctor._2;
            let h = ctor._3;
            ifres = %equal()(v', v) && (%equal()(getId(l), idl) && %equal()(getId(h), idh)) ? n : lookup(ns);
          } else {
            let ifres;
            if (false) {
              ifres = undefined;
            } else {
              throw "Match_failure";
              ifres = undefined;
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      }
      return ifres;
    };
    ifres = lookup(bucket);
  }
  return ifres;
};

let cmpVar = (_arg0, _arg1) => %lessthan()(y, x) ? "LESS" : (%greaterthan()(y, x) ? "GREATER" : "EQUAL");

let zero = "Zero";

let one = "One";

let mkVar = x => mkNode(one, x, zero);

let cacheSize = 1999;

let andslot1 = Belt.Array.make(0, cacheSize);

let andslot2 = Belt.Array.make(0, cacheSize);

let andslot3 = Belt.Array.make(zero, cacheSize);

let xorslot1 = Belt.Array.make(0, cacheSize);

let xorslot2 = Belt.Array.make(0, cacheSize);

let xorslot3 = Belt.Array.make(zero, cacheSize);

let notslot1 = Belt.Array.make(0, cacheSize);

let notslot2 = Belt.Array.make(one, cacheSize);

let hash = (x, y) => %mod()(cacheSize, %add()(y, undefined));

let not;

not = n => {
  let ifres;
  if (n === "Zero") {
    ifres = "One";
  } else {
    let ifres;
    if (n === "One") {
      ifres = "Zero";
    } else {
      let ctor = n;
      let ifres;
      if (ctor.TAG === "Node") {
        let l = ctor._0;
        let v = ctor._1;
        let id = ctor._2;
        let r = ctor._3;
        let h = %mod()(cacheSize, id);
        let ifres;
        if (%equal()(undefined, id)) {
          ifres = undefined;
        } else {
          let f = mkNode(not(r), v, not(l));
          ifres = f;
        }
        ifres = ifres;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let and2;

and2 = (n1, n2) => {
  let ctor = n1;
  let ifres;
  if (ctor.TAG === "Node") {
    let l1 = ctor._0;
    let v1 = ctor._1;
    let i1 = ctor._2;
    let r1 = ctor._3;
    let ctor = n2;
    let ifres;
    if (ctor.TAG === "Node") {
      let l2 = ctor._0;
      let v2 = ctor._1;
      let i2 = ctor._2;
      let r2 = ctor._3;
      let h = hash(i2, i1);
      let ifres;
      if (%equal()(undefined, i1) && %equal()(undefined, i2)) {
        ifres = undefined;
      } else {
        let match = cmpVar(v2, v1);
        let f = match === "EQUAL" ? mkNode(and2(r2, r1), v1, and2(l2, l1)) : (match === "LESS" ? mkNode(and2(n2, r1), v1, and2(n2, l1)) : (match === "GREATER" ? mkNode(and2(r2, n1), v2, and2(l2, n1)) : undefined));
        ifres = f;
      }
      ifres = ifres;
    } else {
      ifres = n2 === "Zero" ? "Zero" : (n2 === "One" ? n1 : undefined);
    }
    ifres = ifres;
  } else {
    ifres = n1 === "Zero" ? "Zero" : (n1 === "One" ? n2 : undefined);
  }
  return ifres;
};

let xor;

xor = (n1, n2) => {
  let ctor = n1;
  let ifres;
  if (ctor.TAG === "Node") {
    let l1 = ctor._0;
    let v1 = ctor._1;
    let i1 = ctor._2;
    let r1 = ctor._3;
    let ctor = n2;
    let ifres;
    if (ctor.TAG === "Node") {
      let l2 = ctor._0;
      let v2 = ctor._1;
      let i2 = ctor._2;
      let r2 = ctor._3;
      let h = hash(i2, i1);
      let ifres;
      if (%equal()(undefined, i1) && %equal()(undefined, i2)) {
        ifres = undefined;
      } else {
        let match = cmpVar(v2, v1);
        let f = match === "EQUAL" ? mkNode(xor(r2, r1), v1, xor(l2, l1)) : (match === "LESS" ? mkNode(xor(n2, r1), v1, xor(n2, l1)) : (match === "GREATER" ? mkNode(xor(r2, n1), v2, xor(l2, n1)) : undefined));
        ifres = f;
      }
      ifres = ifres;
    } else {
      ifres = n2 === "Zero" ? n1 : (n2 === "One" ? not(n1) : undefined);
    }
    ifres = ifres;
  } else {
    ifres = n1 === "Zero" ? n2 : (n1 === "One" ? not(n2) : undefined);
  }
  return ifres;
};

let hwb = n => {
  let h;
  let g;
  h = (i, j) => %equal()(j, i) ? mkVar(i) : xor(and2(g(%sub()(1, j), i), mkVar(j)), and2(h(%sub()(1, j), i), not(mkVar(j))));
  g = (i, j) => %equal()(j, i) ? mkVar(i) : xor(and2(g(j, %add()(1, i)), mkVar(i)), and2(h(j, %add()(1, i)), not(mkVar(i))));
  return h(%sub()(1, n), 0);
};

let seed = %makeref()(0);

let random = _arg0 => {
  %refset()(%add()(17431, %mul()(25173, seed.contents)), seed);
  return %greaterthan()(0, undefined);
};

let random_vars = n => {
  let vars = Belt.Array.make(false, n);
  for (let i = 0; i <= %sub()(1, n); ++i) {}
  return vars;
};

let bool_equal = (a, b) => {
  let match = [a, b];
  let tuple = match;
  let ifres;
  if (tuple[0] === true) {
    let ifres;
    if (tuple[1] === true) {
      ifres = true;
    } else {
      let tuple = match;
      ifres = tuple[0] === false ? (tuple[1] === false ? true : false) : false;
    }
    ifres = ifres;
  } else {
    let tuple = match;
    ifres = tuple[0] === false ? (tuple[1] === false ? true : false) : false;
  }
  return ifres;
};

let test_hwb = (bdd, vars) => {
  let ntrue = %makeref()(0);
  for (let i = 0; i <= %sub()(1, vars.length); ++i) {
    undefined ? %incr()(ntrue) : undefined;
  }
  return bool_equal(%greaterthan()(0, ntrue.contents) ? undefined : false, eval(vars, bdd));
};

let main = _arg0 => {
  let n = 22;
  let ntests = 100;
  let bdd = hwb(n);
  let succeeded = %makeref()(true);
  for (let i = 1; i <= ntests; ++i) {
    %refset()(succeeded.contents && test_hwb(random_vars(n), bdd), succeeded);
  }
  let ifres;
  if (succeeded.contents) {
    ifres = undefined;
  } else {
    throw "Match_failure";
    ifres = undefined;
  }
  return ifres;
};