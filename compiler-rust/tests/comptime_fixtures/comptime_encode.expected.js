let obj = Js_dict.empty();
Js_dict.set(obj, "name", Js_json.string(myUser.name));
Js_dict.set(obj, "age", Js_json.number(myUser.age));
let json = Js_json.object_(obj);
