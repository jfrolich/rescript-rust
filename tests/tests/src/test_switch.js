let f = x => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "A") {
    ifres = 0;
  } else {
    let ctor = x;
    let ifres;
    if (ctor.TAG === "B") {
      ifres = 1;
    } else {
      let ctor = x;
      let ifres;
      if (ctor.TAG === "C") {
        ifres = 2;
      } else {
        let ctor = x;
        ifres = ctor.TAG === "F" ? 3 : (x === "G" ? 4 : (x === "H" ? 5 : undefined));
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let bind = (x, f) => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "Left") {
    let x = ctor._0;
    ifres = {TAG: "Left", _0: f(x)};
  } else {
    let y = x;
    let ctor = x;
    ifres = ctor.TAG === "Error" ? y : undefined;
  }
  return ifres;
};