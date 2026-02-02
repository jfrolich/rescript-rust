let decodeGroup = group => {
  let record = group;
  let ctor = record.id;
  let ifres;
  if (ctor.TAG === "String") {
    let id = ctor._0;
    let ctor = record.name;
    let ifres;
    if (ctor.TAG === "String") {
      let name = ctor._0;
      ifres = [id, name];
    } else {
      ifres = ["e", "f"];
    }
    ifres = ifres;
  } else {
    ifres = ["e", "f"];
  }
  return ifres;
};

let decodeNull = x => {
  let record = x;
  return record.field === "Null" ? "yes it's null" : "no";
};

let decodeUndefined = x => {
  let record = x;
  return record.field === "Undefined" ? "yes it's undefined" : "no";
};