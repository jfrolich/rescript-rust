let height = x => {
  let ifres;
  if (x === "Empty") {
    ifres = 0;
  } else {
    let ctor = x;
    let ifres;
    if (ctor.TAG === "Node") {
      let h = ctor._4;
      ifres = h;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let create = (l, x, d, r) => {
  let hl = height(l);
  let hr = height(r);
  return {TAG: "Node", _0: l, _1: x, _2: d, _3: r, _4: %greaterequal()(hr, hl) ? %add()(1, hl) : %add()(1, hr)};
};

let bal = (l, x, d, r) => {
  let ifres;
  if (l === "Empty") {
    ifres = 0;
  } else {
    let ctor = l;
    let ifres;
    if (ctor.TAG === "Node") {
      let h = ctor._4;
      ifres = h;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  let hl = ifres;
  let ifres;
  if (r === "Empty") {
    ifres = 0;
  } else {
    let ctor = r;
    let ifres;
    if (ctor.TAG === "Node") {
      let h = ctor._4;
      ifres = h;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  let hr = ifres;
  let ifres;
  if (%greaterthan()(%add()(2, hr), hl)) {
    let ifres;
    if (l === "Empty") {
      ifres = Pervasives.invalid_arg("Map.bal");
    } else {
      let ctor = l;
      let ifres;
      if (ctor.TAG === "Node") {
        let ll = ctor._0;
        let lv = ctor._1;
        let ld = ctor._2;
        let lr = ctor._3;
        let ifres;
        if (%greaterequal()(height(lr), height(ll))) {
          ifres = create(create(r, d, x, lr), ld, lv, ll);
        } else {
          let ifres;
          if (lr === "Empty") {
            ifres = Pervasives.invalid_arg("Map.bal");
          } else {
            let ctor = lr;
            let ifres;
            if (ctor.TAG === "Node") {
              let lrl = ctor._0;
              let lrv = ctor._1;
              let lrd = ctor._2;
              let lrr = ctor._3;
              ifres = create(create(r, d, x, lrr), lrd, lrv, create(lrl, ld, lv, ll));
            } else {
              ifres = undefined;
            }
            ifres = ifres;
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  } else {
    let ifres;
    if (%greaterthan()(%add()(2, hl), hr)) {
      let ifres;
      if (r === "Empty") {
        ifres = Pervasives.invalid_arg("Map.bal");
      } else {
        let ctor = r;
        let ifres;
        if (ctor.TAG === "Node") {
          let rl = ctor._0;
          let rv = ctor._1;
          let rd = ctor._2;
          let rr = ctor._3;
          let ifres;
          if (%greaterequal()(height(rl), height(rr))) {
            ifres = create(rr, rd, rv, create(rl, d, x, l));
          } else {
            let ifres;
            if (rl === "Empty") {
              ifres = Pervasives.invalid_arg("Map.bal");
            } else {
              let ctor = rl;
              let ifres;
              if (ctor.TAG === "Node") {
                let rll = ctor._0;
                let rlv = ctor._1;
                let rld = ctor._2;
                let rlr = ctor._3;
                ifres = create(create(rr, rd, rv, rlr), rld, rlv, create(rll, d, x, l));
              } else {
                ifres = undefined;
              }
              ifres = ifres;
            }
            ifres = ifres;
          }
          ifres = ifres;
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      }
      ifres = ifres;
    } else {
      ifres = {TAG: "Node", _0: l, _1: x, _2: d, _3: r, _4: %greaterequal()(hr, hl) ? %add()(1, hl) : %add()(1, hr)};
    }
    ifres = ifres;
  }
  return ifres;
};

let add;

add = (x, data, compare, x_) => {
  let ifres;
  if (x_ === "Empty") {
    ifres = {TAG: "Node", _0: "Empty", _1: x, _2: data, _3: "Empty", _4: 1};
  } else {
    let ctor = x_;
    let ifres;
    if (ctor.TAG === "Node") {
      let l = ctor._0;
      let v = ctor._1;
      let d = ctor._2;
      let r = ctor._3;
      let h = ctor._4;
      let c = compare(v, x);
      ifres = %equal()(0, c) ? {TAG: "Node", _0: l, _1: x, _2: data, _3: r, _4: h} : (%lessthan()(0, c) ? bal(r, d, v, add(l, compare, data, x)) : bal(add(r, compare, data, x), d, v, l));
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let add = (x, data, _arg2) => {compare: v.compare, data: add(v.data, Comparable.getcompare(X.compare), data, x)};

let empty = _arg0 => {compare: v, data: "Empty"};

let v0 = empty(undefined);

let v1 = empty(undefined);

let v3 = add(v0, "a", 3);

console.log()(v3);