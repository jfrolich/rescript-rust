let doStuffWithResult = s => s === "s" ? {TAG: "Ok", _0: "hello"} : {TAG: "Error", _0: "InvalidString"};

let doNextStuffWithResult = s => s === "s" ? {TAG: "Ok", _0: "hello"} : {TAG: "Error", _0: "InvalidNext"};

let getXWithResult = s => {
  let match = doStuffWithResult(s);
  let y = match;
  let ctor = match;
  let ifres;
  if (ctor.TAG === "Error") {
    ifres = y;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Ok") {
      let y = ctor._0;
      let match = doNextStuffWithResult(y);
      let x = match;
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Error") {
        ifres = x;
      } else {
        let ctor = match;
        let ifres;
        if (ctor.TAG === "Ok") {
          let x = ctor._0;
          ifres = {TAG: "Ok", _0: x + y};
        } else {
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

let match = getXWithResult("s");

let ctor = match;

let ifres;

if (ctor.TAG === "Ok") {
  let x = ctor._0;
  ifres = x;
} else {
  let ctor = match;
  let ifres;
  if (ctor.TAG === "Error") {
    let poly = ctor._0;
    let ifres;
    if (poly[0] === "InvalidString") {
      ifres = "nope";
    } else {
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Error") {
        let poly = ctor._0;
        ifres = poly[0] === "InvalidNext" ? "nope!" : undefined;
      } else {
        ifres = undefined;
      }
      ifres = ifres;
    }
    ifres = ifres;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Error") {
      let poly = ctor._0;
      ifres = poly[0] === "InvalidNext" ? "nope!" : undefined;
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  ifres = ifres;
}

let someResult = ifres;

let doStuffWithOption = s => s === "s" ? {TAG: "Some", _0: "hello"} : "None";

let doNextStuffWithOption = s => s === "s" ? {TAG: "Some", _0: "hello"} : "None";

let getXWithOption = s => {
  let match = doStuffWithOption(s);
  let y = match;
  let ifres;
  if (match === "None") {
    ifres = y;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Some") {
      let y = ctor._0;
      let match = doNextStuffWithOption(y);
      let x = match;
      let ifres;
      if (match === "None") {
        ifres = x;
      } else {
        let ctor = match;
        let ifres;
        if (ctor.TAG === "Some") {
          let x = ctor._0;
          ifres = {TAG: "Some", _0: x + y};
        } else {
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

let match = getXWithOption("s");

let ctor = match;

let ifres;

if (ctor.TAG === "Some") {
  let x = ctor._0;
  ifres = x;
} else {
  ifres = match === "None" ? "nope" : undefined;
}

let someOption = ifres;

let doStuffResultAsync = s => (prim => prim)(s === "s" ? {TAG: "Ok", _0: {s: "hello"}} : {TAG: "Error", _0: "FetchError"});

let decodeResAsync = res => {
  let match = res.s;
  let call = (prim => prim)(match === "s" ? {TAG: "Ok", _0: res.s} : {TAG: "Error", _0: "DecodeError"});
  return call;
};

let getXWithResultAsync = s => {
  let match = await doStuffResultAsync(s);
  let x = match;
  let ctor = match;
  let ifres;
  if (ctor.TAG === "Error") {
    ifres = x;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Ok") {
      let res = ctor._0;
      let record = ctor._0;
      let s = record.s;
      console.log()(s);
      let match = await decodeResAsync(res);
      let x = match;
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Error") {
        ifres = x;
      } else {
        let ctor = match;
        let ifres;
        if (ctor.TAG === "Ok") {
          let x = ctor._0;
          ifres = {TAG: "Ok", _0: x};
        } else {
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
  let call = (prim => prim)(ifres);
  return call;
};

let returnsAliasOnFirstError = s => {
  let match = doStuffWithResult(s);
  let _y = match;
  let ctor = match;
  let ifres;
  if (ctor.TAG === "Error") {
    ifres = _y;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Ok") {
      let _y = ctor._0;
      ifres = {TAG: "Ok", _0: "ok"};
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let returnsAliasOnSecondError = s => {
  let match = doStuffWithResult(s);
  let y = match;
  let ctor = match;
  let ifres;
  if (ctor.TAG === "Error") {
    ifres = y;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Ok") {
      let y = ctor._0;
      let match = doNextStuffWithResult(y);
      let _x = match;
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Error") {
        ifres = _x;
      } else {
        let ctor = match;
        let ifres;
        if (ctor.TAG === "Ok") {
          let _x = ctor._0;
          ifres = {TAG: "Ok", _0: "ok"};
        } else {
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

let returnsAliasOnOk = s => {
  let match = doStuffWithResult(s);
  let _e = match;
  let ctor = match;
  let ifres;
  if (ctor.TAG === "Ok") {
    ifres = _e;
  } else {
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Error") {
      let _e = ctor._0;
      ifres = {TAG: "Error", _0: "GotError"};
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};