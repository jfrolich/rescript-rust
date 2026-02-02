let func = _arg0 => {
  let ifres;
  if (state === "Empty") {
    ifres = 0;
  } else {
    let ctor = state;
    let ifres;
    if (ctor.TAG === "Int2") {
      let intValue = ctor._0;
      let intFunc = intParam => intParam + intValue;
      ifres = intFunc(0);
    } else {
      let ctor = state;
      let ifres;
      if (ctor.TAG === "Int1") {
        let intValue = ctor._0;
        let intFunc = intParam => intParam + intValue;
        ifres = intFunc(0);
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  }
  return ifres;
};