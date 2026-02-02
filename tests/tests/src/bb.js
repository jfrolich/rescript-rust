let f = x => {
  let poly = x;
  let ifres;
  if (poly[0] === "a") {
    ifres = "a";
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "b") {
      ifres = "b";
    } else {
      let poly = x;
      ifres = poly[0] === "c" ? "c" : undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let ff = x => {
  let ifres;
  if (x === "a") {
    ifres = "a";
  } else {
    let ifres;
    if (x === "b") {
      ifres = "b";
    } else {
      let ifres;
      if (x === "c") {
        ifres = "c";
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
    }
    ifres = ifres;
  }
  return ifres;
};

let test = x => {
  let ifres;
  if (x === "a") {
    ifres = "a";
  } else {
    let ifres;
    if (x === "b") {
      ifres = "b";
    } else {
      let ifres;
      if (x === "c") {
        ifres = "c";
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
    }
    ifres = ifres;
  }
  let match = ifres;
  let poly = match;
  let ifres;
  if (poly[0] === "a") {
    ifres = "a";
  } else {
    let poly = match;
    let ifres;
    if (poly[0] === "b") {
      ifres = "b";
    } else {
      let poly = match;
      ifres = poly[0] === "c" ? "c" : undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let match = "a";

let poly = match;

let ifres;

if (poly[0] === "a") {
  ifres = "a";
} else {
  let poly = match;
  let ifres;
  if (poly[0] === "b") {
    ifres = "b";
  } else {
    let poly = match;
    ifres = poly[0] === "c" ? "c" : undefined;
  }
  ifres = ifres;
}

let test_poly = ifres;

let tuple = [f("a"), f("b"), f("c")];

let c = tuple[0];

let d = tuple[1];

let e = tuple[2];