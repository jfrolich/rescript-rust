let g = x => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "A") {
    let v = ctor._0;
    ifres = v(x);
  } else {
    ifres = undefined;
  }
  return ifres;
};

let loop = g({TAG: "A", _0: g});

let non_terminate = (x => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "A") {
    let v = ctor._0;
    ifres = v(x);
  } else {
    ifres = undefined;
  }
  return ifres;
})({TAG: "A", _0: g});

let xx;

xx = {xx: xx};