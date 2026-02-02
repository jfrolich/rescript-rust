let user = {TAG: "User", _0: {name: "Corentin", age: 35}};

let getName = t => {
  let ctor = t;
  let ifres;
  if (ctor.TAG === "User") {
    let record = ctor._0;
    let name = record.name;
    ifres = name;
  } else {
    ifres = undefined;
  }
  return ifres;
};

let getName' = t => {
  let ctor = t;
  let ifres;
  if (ctor.TAG === "User") {
    let u = ctor._0;
    ifres = u.name;
  } else {
    ifres = undefined;
  }
  return ifres;
};

let getAge = t => {
  let ctor = t;
  let ifres;
  if (ctor.TAG === "User") {
    let record = ctor._0;
    let age = record.age;
    ifres = age;
  } else {
    ifres = undefined;
  }
  return ifres;
};

let getAge' = t => {
  let ctor = t;
  let ifres;
  if (ctor.TAG === "User") {
    let u = ctor._0;
    ifres = u.age;
  } else {
    ifres = undefined;
  }
  return ifres;
};