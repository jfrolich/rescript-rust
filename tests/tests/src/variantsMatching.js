let toEnum = x => x === "A" ? 0 : (x === "B" ? 1 : (x === "C" ? 2 : (x === "D" ? 3 : (x === "Pi" ? 5 : undefined))));

let toString = x => x === "A" ? "A" : (x === "B" ? "B" : (x === "C" ? "C" : (x === "D" ? "D" : (x === "Pi" ? "Pi" : undefined))));

let bar = x => x === "A" ? 10 : (x === "B" ? 0 : (x === "C" ? 0 : (x === "D" ? 0 : (x === "Pi" ? 10 : undefined))));

let and_ = (x, y) => {
  let match = [x, y];
  let tuple = match;
  let ifres;
  if (tuple[0] === "True") {
    let ifres;
    if (tuple[1] === "False") {
      ifres = "False";
    } else {
      let tuple = match;
      let ifres;
      if (tuple[0] === "False") {
        let ifres;
        if (tuple[1] === "True") {
          ifres = "False";
        } else {
          let tuple = match;
          let ifres;
          if (tuple[0] === "False") {
            let ifres;
            if (tuple[1] === "False") {
              ifres = "False";
            } else {
              let tuple = match;
              ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
            }
            ifres = ifres;
          } else {
            let tuple = match;
            ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        let tuple = match;
        let ifres;
        if (tuple[0] === "False") {
          let ifres;
          if (tuple[1] === "False") {
            ifres = "False";
          } else {
            let tuple = match;
            ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
        }
        ifres = ifres;
      }
      ifres = ifres;
    }
    ifres = ifres;
  } else {
    let tuple = match;
    let ifres;
    if (tuple[0] === "False") {
      let ifres;
      if (tuple[1] === "True") {
        ifres = "False";
      } else {
        let tuple = match;
        let ifres;
        if (tuple[0] === "False") {
          let ifres;
          if (tuple[1] === "False") {
            ifres = "False";
          } else {
            let tuple = match;
            ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
          }
          ifres = ifres;
        } else {
          let tuple = match;
          ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
        }
        ifres = ifres;
      }
      ifres = ifres;
    } else {
      let tuple = match;
      let ifres;
      if (tuple[0] === "False") {
        let ifres;
        if (tuple[1] === "False") {
          ifres = "False";
        } else {
          let tuple = match;
          ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
        }
        ifres = ifres;
      } else {
        let tuple = match;
        ifres = tuple[0] === "True" ? (tuple[1] === "True" ? "True" : undefined) : undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let id = x => x === "True" ? "True" : (x === "False" ? "False" : undefined);

let not_ = x => x === "True" ? "False" : (x === "False" ? "True" : undefined);

let st = state => {
  let ifres;
  if (state === "Empty") {
    ifres = 0;
  } else {
    let ctor = state;
    let ifres;
    if (ctor.TAG === "Int2") {
      let intValue = ctor._0;
      ifres = 23;
    } else {
      let ctor = state;
      let ifres;
      if (ctor.TAG === "Int1") {
        let intValue = ctor._0;
        ifres = 23;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let showToJs = x => {
  let ifres;
  if (x === "Yes") {
    ifres = true;
  } else {
    let ctor = x;
    ifres = ctor.TAG === "After" ? true : (x === "No" ? false : undefined);
  }
  return ifres;
};

let third = l => {
  let ctor = l;
  let ifres;
  if (ctor.TAG === "::") {
    let ifres;
    if (ctor._0 === 1) {
      let ctor = ctor._1;
      let ifres;
      if (ctor.TAG === "::") {
        let ifres;
        if (ctor._0 === 2) {
          let ctor = ctor._1;
          ifres = ctor.TAG === "::" ? (ctor._0 === 3 ? (ctor._1 === "[]" ? true : false) : false) : false;
        } else {
          ifres = false;
        }
        ifres = ifres;
      } else {
        ifres = false;
      }
      ifres = ifres;
    } else {
      ifres = false;
    }
    ifres = ifres;
  } else {
    ifres = false;
  }
  return ifres;
};

let third2 = l => {
  let ctor = l;
  let ifres;
  if (ctor.TAG === "Cons") {
    let ifres;
    if (ctor._0 === 1) {
      let ctor = ctor._1;
      let ifres;
      if (ctor.TAG === "Cons") {
        let ifres;
        if (ctor._0 === 2) {
          let ctor = ctor._1;
          ifres = ctor.TAG === "Cons" ? (ctor._0 === 3 ? (ctor._1 === "Empty" ? true : false) : false) : false;
        } else {
          ifres = false;
        }
        ifres = ifres;
      } else {
        ifres = false;
      }
      ifres = ifres;
    } else {
      ifres = false;
    }
    ifres = ifres;
  } else {
    ifres = false;
  }
  return ifres;
};