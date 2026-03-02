let a1 = "A1";

let a2 = "A2";

let b = {TAG: "B", _0: 34};

let c = {TAG: "C", _0: 4, _1: 2};

let d = {TAG: "D", _0: [4, 2]};

let foo = x => {
  let ifres;
  if (x === "A1") {
    ifres = 1;
  } else {
    let ifres;
    if (x === "A2") {
      ifres = 2;
    } else {
      let ctor = x;
      let ifres;
      if (ctor.TAG === "B") {
        let n = ctor._0;
        ifres = n;
      } else {
        let ctor = x;
        let ifres;
        if (ctor.TAG === "C") {
          let n = ctor._0;
          let m = ctor._1;
          ifres = %add()(m, n);
        } else {
          let ctor = x;
          let ifres;
          if (ctor.TAG === "D") {
            let tuple = ctor._0;
            let n = tuple[0];
            let m = tuple[1];
            ifres = %add()(m, n);
          } else {
            ifres = undefined;
          }
          ifres = ifres;
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let fooA1 = x => x === "A1" ? 1 : 42;

let fooC = x => {
  let ctor = x;
  let ifres;
  if (ctor.TAG === "C") {
    let n = ctor._0;
    let m = ctor._1;
    ifres = %add()(m, n);
  } else {
    ifres = 42;
  }
  return ifres;
};

let switchNum = x => x === 0 ? "0" : (x === 1 ? "1" : (x === 2 ? "2" : "_"));

let rollback_path = (subst, p) => {
  try {
    "try";
  } catch (exn) {
    let ctor = p;
    let ifres;
    if (ctor.TAG === "Pident") {
      ifres = "Pident | Papply";
    } else {
      let ctor = p;
      let ifres;
      if (ctor.TAG === "Papply") {
        ifres = "Pident | Papply";
      } else {
        let ctor = p;
        ifres = ctor.TAG === "Pdot" ? "Pdot" : undefined;
      }
      ifres = ifres;
    }
    
  }
  
};

let fooExn = f => {
  try {
    f("()");
  } catch (exn) {
    1;
  }
  
};