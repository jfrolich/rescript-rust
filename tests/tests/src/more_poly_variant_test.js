let map;

map = f => (x => {
  let poly = x;
  let ifres;
  if (poly[0] === "Nil") {
    ifres = "Nil";
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "Cons") {
      let tuple = poly[1];
      let a = tuple[0];
      let l = tuple[1];
      ifres = {NAME: "Cons", VAL: [f(a), map(f)(l)]};
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
});

let split_cases = x => {
  let x = x;
  let poly = x;
  let ifres;
  if (poly[0] === "Nil") {
    ifres = {NAME: "A", VAL: x};
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "Cons") {
      ifres = {NAME: "A", VAL: x};
    } else {
      let x = x;
      let poly = x;
      ifres = poly[0] === "Snoc" ? {NAME: "B", VAL: x} : undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let f = x => {
  let poly = x;
  let ifres;
  if (poly[0] === "Tag1") {
    ifres = "myvariant";
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "Tag2") {
      ifres = "myvariant";
    } else {
      let poly = x;
      ifres = poly[0] === "Tag3" ? "Tag3" : undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let g1 = x => {
  let poly = x;
  let ifres;
  if (poly[0] === "Tag1") {
    ifres = "Tag1";
  } else {
    let poly = x;
    ifres = poly[0] === "Tag2" ? "Tag2" : undefined;
  }
  return ifres;
};

let g = x => {
  let x = x;
  let poly = x;
  let ifres;
  if (poly[0] === "Tag1") {
    ifres = g1(x);
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "Tag2") {
      ifres = g1(x);
    } else {
      let poly = x;
      ifres = poly[0] === "Tag3" ? "Tag3" : undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let f1 = x => {
  let poly = x;
  let ifres;
  if (poly[0] === "As") {
    ifres = "A";
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "C") {
      ifres = "other";
    } else {
      let poly = x;
      let ifres;
      if (poly[0] === "A") {
        ifres = "other";
      } else {
        let poly = x;
        ifres = poly[0] === "B" ? "other" : undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};

let f2 = x => {
  let x = x;
  let poly = x;
  let ifres;
  if (poly[0] === "Tag3") {
    console.log()(x);
    ifres = 2;
  } else {
    let poly = x;
    let ifres;
    if (poly[0] === "Tag4") {
      console.log()(x);
      ifres = 2;
    } else {
      let poly = x;
      let ifres;
      if (poly[0] === "Tag1") {
        console.log()(x);
        ifres = 2;
      } else {
        let poly = x;
        let ifres;
        if (poly[0] === "Tag2") {
          console.log()(x);
          ifres = 2;
        } else {
          let poly = x;
          let ifres;
          if (poly[0] === "hello") {
            ifres = 3;
          } else {
            let poly = x;
            let ifres;
            if (poly[0] === "h") {
              ifres = 2;
            } else {
              let poly = x;
              let ifres;
              if (poly[0] === "a") {
                ifres = 333;
              } else {
                let poly = x;
                let ifres;
                if (poly[0] === "b") {
                  ifres = 333;
                } else {
                  let poly = x;
                  ifres = poly[0] === "c" ? 333 : undefined;
                }
                ifres = ifres;
              }
              ifres = ifres;
            }
            ifres = ifres;
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