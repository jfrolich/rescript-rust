let treeHeight = _arg0 => {
  let ifres;
  if (n === "None") {
    ifres = 0;
  } else {
    let ctor = n;
    let ifres;
    if (ctor.TAG === "Some") {
      let n = ctor._0;
      ifres = n.height;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let copy;

copy = n => {
  let ifres;
  if (n === "None") {
    ifres = n;
  } else {
    let ctor = n;
    let ifres;
    if (ctor.TAG === "Some") {
      let record = ctor._0;
      let v = record.value;
      let h = record.height;
      let l = record.left;
      let r = record.right;
      ifres = {TAG: "Some", _0: {value: v, height: h, left: copy(l), right: copy(r)}};
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};