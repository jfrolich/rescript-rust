describe()(_arg0 => {
  test()(_arg0 => {
    let v = parse()(" { \"x\" : [1, 2, 3 ] } ");
    let ty = J.classify(v);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONObject") {
      let x = ctor._0;
      let match = Js.Dict.get("x", x);
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Some") {
        let v = ctor._0;
        let ty2 = J.classify(v);
        let ctor = ty2;
        let ifres;
        if (ctor.TAG === "JSONArray") {
          let x = ctor._0;
          forEach()(x => {
            let ty3 = J.classify(x);
            let ctor = ty3;
            let ifres;
            if (ctor.TAG === "JSONNumber") {
              ifres = "()";
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
            return ifres;
          }, x);
          ifres = Test_utils.ok(true, %loc_LOC());
        } else {
          ifres = Test_utils.ok(false, %loc_LOC());
        }
        ifres = ifres;
      } else {
        ifres = match === "None" ? Test_utils.ok(false, %loc_LOC()) : undefined;
      }
      ifres = ifres;
    } else {
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    
    return Test_utils.eq(true, J.test({TAG: "Object"}, v), %loc_LOC());
  }, "JSON object parsing and validation");
  test()(_arg0 => {
    let json = parse()(stringify()(null()));
    let ty = J.classify(json);
    let ifres;
    if (ty === "JSONNull") {
      ifres = Test_utils.ok(true, %loc_LOC());
    } else {
      console.log()(ty);
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    return ifres;
  }, "JSON null parsing");
  test()(_arg0 => {
    let json = parse()(stringify()((prim => prim)("test string")));
    let ty = J.classify(json);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONString") {
      let x = ctor._0;
      ifres = Test_utils.eq("test string", x, %loc_LOC());
    } else {
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    return ifres;
  }, "JSON string parsing");
  test()(_arg0 => {
    let json = parse()(stringify()((prim => prim)(1.23456789)));
    let ty = J.classify(json);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONNumber") {
      let x = ctor._0;
      ifres = Test_utils.eq(1.23456789, x, %loc_LOC());
    } else {
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    return ifres;
  }, "JSON number parsing");
  test()(_arg0 => {
    let json = parse()(stringify()((prim => prim)(undefined)));
    let ty = J.classify(json);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONNumber") {
      let x = ctor._0;
      ifres = Test_utils.eq(-1347440721, undefined, %loc_LOC());
    } else {
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    return ifres;
  }, "JSON large integer parsing");
  test()(_arg0 => {
    let test = v => {
      let json = parse()(stringify()((prim => prim)(v)));
      let ty = J.classify(json);
      return ty === "JSONTrue" ? Test_utils.eq(v, true, %loc_LOC()) : (ty === "JSONFalse" ? Test_utils.eq(v, false, %loc_LOC()) : Test_utils.ok(false, %loc_LOC()));
    };
    test(true);
    return test(false);
  }, "JSON boolean parsing");
  test()(_arg0 => {
    let option_get = x => {
      let ifres;
      if (x === "None") {
        let ifres;
        if (false) {
          ifres = undefined;
        } else {
          throw "Match_failure";
          ifres = undefined;
        }
        ifres = ifres;
      } else {
        let ctor = x;
        let ifres;
        if (ctor.TAG === "Some") {
          let x = ctor._0;
          ifres = x;
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      }
      return ifres;
    };
    let dict = ()("()");
    ()((prim => prim)("test string"), "a", dict);
    ()((prim => prim)(123.0), "b", dict);
    let json = parse()(stringify()((prim => prim)(dict)));
    let ty = J.classify(json);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONObject") {
      let x = ctor._0;
      let ta = J.classify(option_get(Js_dict.get("a", x)));
      let ctor = ta;
      let ifres;
      if (ctor.TAG === "JSONString") {
        let a = ctor._0;
        let ifres;
        if (%notequal()("test string", a)) {
          ifres = Test_utils.ok(false, %loc_LOC());
        } else {
          let ty = J.classify(option_get(Js_dict.get("b", x)));
          let ctor = ty;
          let ifres;
          if (ctor.TAG === "JSONNumber") {
            let b = ctor._0;
            ifres = Test_utils.approxEq(b, 123.0, 0.001, %loc_LOC());
          } else {
            ifres = Test_utils.ok(false, %loc_LOC());
          }
          ifres = ifres;
        }
        ifres = ifres;
      } else {
        ifres = Test_utils.ok(false, %loc_LOC());
      }
      ifres = ifres;
    } else {
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    return ifres;
  }, "JSON object with string and number fields");
  let eq_at_i = (_arg0, _arg1, _arg2, _arg3, _arg4) => {
    let ty = J.classify(json);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONArray") {
      let x = ctor._0;
      let ty = J.classify(undefined);
      let ctor = kind;
      let ifres;
      if (ctor.TAG === "Boolean") {
        ifres = ty === "JSONTrue" ? Test_utils.eq(expected, true, loc) : (ty === "JSONFalse" ? Test_utils.eq(expected, false, loc) : Test_utils.ok(false, loc));
      } else {
        let ctor = kind;
        let ifres;
        if (ctor.TAG === "Number") {
          let ctor = ty;
          let ifres;
          if (ctor.TAG === "JSONNumber") {
            let f = ctor._0;
            ifres = Test_utils.eq(expected, f, loc);
          } else {
            ifres = Test_utils.ok(false, loc);
          }
          ifres = ifres;
        } else {
          let ctor = kind;
          let ifres;
          if (ctor.TAG === "Object") {
            let ctor = ty;
            let ifres;
            if (ctor.TAG === "JSONObject") {
              let f = ctor._0;
              ifres = Test_utils.eq(expected, f, loc);
            } else {
              ifres = Test_utils.ok(false, loc);
            }
            ifres = ifres;
          } else {
            let ctor = kind;
            let ifres;
            if (ctor.TAG === "Array") {
              let ctor = ty;
              let ifres;
              if (ctor.TAG === "JSONArray") {
                let f = ctor._0;
                ifres = Test_utils.eq(expected, f, loc);
              } else {
                ifres = Test_utils.ok(false, loc);
              }
              ifres = ifres;
            } else {
              let ctor = kind;
              let ifres;
              if (ctor.TAG === "Null") {
                ifres = ty === "JSONNull" ? Test_utils.ok(true, loc) : Test_utils.ok(false, loc);
              } else {
                let ctor = kind;
                let ifres;
                if (ctor.TAG === "String") {
                  let ctor = ty;
                  let ifres;
                  if (ctor.TAG === "JSONString") {
                    let f = ctor._0;
                    ifres = Test_utils.eq(expected, f, loc);
                  } else {
                    ifres = Test_utils.ok(false, loc);
                  }
                  ifres = ifres;
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
        ifres = ifres;
      }
      ifres = ifres;
    } else {
      ifres = Test_utils.ok(false, loc);
    }
    return ifres;
  };
  test()(_arg0 => {
    let json = parse()(stringify()((prim => prim)(Belt.Array.map(prim => prim, ["string 0", "string 1", "string 2"]))));
    eq_at_i("string 0", {TAG: "String"}, 0, json, %loc_LOC());
    eq_at_i("string 1", {TAG: "String"}, 1, json, %loc_LOC());
    return eq_at_i("string 2", {TAG: "String"}, 2, json, %loc_LOC());
  }, "JSON string array parsing");
  test()(_arg0 => {
    let json = parse()(stringify()((prim => prim)(["string 0", "string 1", "string 2"])));
    eq_at_i("string 0", {TAG: "String"}, 0, json, %loc_LOC());
    eq_at_i("string 1", {TAG: "String"}, 1, json, %loc_LOC());
    return eq_at_i("string 2", {TAG: "String"}, 2, json, %loc_LOC());
  }, "JSON stringArray parsing");
  test()(_arg0 => {
    let a = [1.0000001, 10000000000.1, 123.0];
    let json = parse()(stringify()((prim => prim)(a)));
    eq_at_i(undefined, {TAG: "Number"}, 0, json, %loc_LOC());
    eq_at_i(undefined, {TAG: "Number"}, 1, json, %loc_LOC());
    return eq_at_i(undefined, {TAG: "Number"}, 2, json, %loc_LOC());
  }, "JSON number array parsing");
  test()(_arg0 => {
    let a = [0, -1347440721, -268391749];
    let json = parse()(stringify()((prim => prim)(Belt.Array.map(prim0 => {
      
    }, a))));
    eq_at_i(undefined, {TAG: "Number"}, 0, json, %loc_LOC());
    eq_at_i(undefined, {TAG: "Number"}, 1, json, %loc_LOC());
    return eq_at_i(undefined, {TAG: "Number"}, 2, json, %loc_LOC());
  }, "JSON integer array parsing");
  test()(_arg0 => {
    let a = [true, false, true];
    let json = parse()(stringify()((prim => prim)(a)));
    eq_at_i(undefined, {TAG: "Boolean"}, 0, json, %loc_LOC());
    eq_at_i(undefined, {TAG: "Boolean"}, 1, json, %loc_LOC());
    return eq_at_i(undefined, {TAG: "Boolean"}, 2, json, %loc_LOC());
  }, "JSON boolean array parsing");
  test()(_arg0 => {
    let option_get = x => {
      let ifres;
      if (x === "None") {
        let ifres;
        if (false) {
          ifres = undefined;
        } else {
          throw "Match_failure";
          ifres = undefined;
        }
        ifres = ifres;
      } else {
        let ctor = x;
        let ifres;
        if (ctor.TAG === "Some") {
          let x = ctor._0;
          ifres = x;
        } else {
          ifres = undefined;
        }
        ifres = ifres;
      }
      return ifres;
    };
    let make_d = (s, i) => {
      let d = ()("()");
      ()((prim => prim)(s), "a", d);
      ()((prim => prim)(undefined), "b", d);
      return d;
    };
    let a = [make_d(123, "aaa"), make_d(456, "bbb")];
    let json = parse()(stringify()((prim => prim)(a)));
    let ty = J.classify(json);
    let ctor = ty;
    let ifres;
    if (ctor.TAG === "JSONArray") {
      let x = ctor._0;
      let ty = J.classify(undefined);
      let ctor = ty;
      let ifres;
      if (ctor.TAG === "JSONObject") {
        let a1 = ctor._0;
        let ty = J.classify(option_get(Js_dict.get("a", a1)));
        let ctor = ty;
        let ifres;
        if (ctor.TAG === "JSONString") {
          let aValue = ctor._0;
          ifres = Test_utils.eq("bbb", aValue, %loc_LOC());
        } else {
          ifres = Test_utils.ok(false, %loc_LOC());
        }
        ifres = ifres;
      } else {
        ifres = Test_utils.ok(false, %loc_LOC());
      }
      ifres = ifres;
    } else {
      ifres = Test_utils.ok(false, %loc_LOC());
    }
    return ifres;
  }, "JSON object array parsing");
  test()(_arg0 => {
    let invalid_json_str = "{{ A}";
    try {
      Test_utils.ok(false, %loc_LOC());
    } catch (exn) {
      Test_utils.ok(true, %loc_LOC());
    }
    
  }, "JSON invalid parsing");
  test()(_arg0 => Test_utils.eq({TAG: "Some", _0: "[1,2,3]"}, stringify()([1, 2, 3]), %loc_LOC()), "JSON stringifyAny array");
  test()(_arg0 => Test_utils.eq({TAG: "Some", _0: "{\"foo\":1,\"bar\":\"hello\",\"baz\":{\"baaz\":10}}"}, stringify()(()(()(10), "hello", 1)), %loc_LOC()), "JSON stringifyAny object");
  test()(_arg0 => Test_utils.eq({TAG: "Some", _0: "null"}, stringify()(null), %loc_LOC()), "JSON stringifyAny null");
  test()(_arg0 => Test_utils.eq("None", stringify()(undefined), %loc_LOC()), "JSON stringifyAny undefined");
  test()(_arg0 => {
    Test_utils.eq({TAG: "Some", _0: "test"}, J.decodeString((prim => prim)("test")), %loc_LOC());
    Test_utils.eq("None", J.decodeString((prim => prim)(true)), %loc_LOC());
    Test_utils.eq("None", J.decodeString((prim => prim)([])), %loc_LOC());
    Test_utils.eq("None", J.decodeString(null()), %loc_LOC());
    Test_utils.eq("None", J.decodeString((prim => prim)(()("()"))), %loc_LOC());
    return Test_utils.eq("None", J.decodeString((prim => prim)(1.23)), %loc_LOC());
  }, "JSON decodeString");
  test()(_arg0 => {
    Test_utils.eq("None", J.decodeNumber((prim => prim)("test")), %loc_LOC());
    Test_utils.eq("None", J.decodeNumber((prim => prim)(true)), %loc_LOC());
    Test_utils.eq("None", J.decodeNumber((prim => prim)([])), %loc_LOC());
    Test_utils.eq("None", J.decodeNumber(null()), %loc_LOC());
    Test_utils.eq("None", J.decodeNumber((prim => prim)(()("()"))), %loc_LOC());
    return Test_utils.eq({TAG: "Some", _0: 1.23}, J.decodeNumber((prim => prim)(1.23)), %loc_LOC());
  }, "JSON decodeNumber");
  test()(_arg0 => {
    Test_utils.eq("None", J.decodeObject((prim => prim)("test")), %loc_LOC());
    Test_utils.eq("None", J.decodeObject((prim => prim)(true)), %loc_LOC());
    Test_utils.eq("None", J.decodeObject((prim => prim)([])), %loc_LOC());
    Test_utils.eq("None", J.decodeObject(null()), %loc_LOC());
    Test_utils.eq({TAG: "Some", _0: ()("()")}, J.decodeObject((prim => prim)(()("()"))), %loc_LOC());
    return Test_utils.eq("None", J.decodeObject((prim => prim)(1.23)), %loc_LOC());
  }, "JSON decodeObject");
  test()(_arg0 => {
    Test_utils.eq("None", J.decodeArray((prim => prim)("test")), %loc_LOC());
    Test_utils.eq("None", J.decodeArray((prim => prim)(true)), %loc_LOC());
    Test_utils.eq({TAG: "Some", _0: []}, J.decodeArray((prim => prim)([])), %loc_LOC());
    Test_utils.eq("None", J.decodeArray(null()), %loc_LOC());
    Test_utils.eq("None", J.decodeArray((prim => prim)(()("()"))), %loc_LOC());
    return Test_utils.eq("None", J.decodeArray((prim => prim)(1.23)), %loc_LOC());
  }, "JSON decodeArray");
  test()(_arg0 => {
    Test_utils.eq("None", J.decodeBoolean((prim => prim)("test")), %loc_LOC());
    Test_utils.eq({TAG: "Some", _0: true}, J.decodeBoolean((prim => prim)(true)), %loc_LOC());
    Test_utils.eq("None", J.decodeBoolean((prim => prim)([])), %loc_LOC());
    Test_utils.eq("None", J.decodeBoolean(null()), %loc_LOC());
    Test_utils.eq("None", J.decodeBoolean((prim => prim)(()("()"))), %loc_LOC());
    return Test_utils.eq("None", J.decodeBoolean((prim => prim)(1.23)), %loc_LOC());
  }, "JSON decodeBoolean");
  test()(_arg0 => {
    Test_utils.eq("None", J.decodeNull((prim => prim)("test")), %loc_LOC());
    Test_utils.eq("None", J.decodeNull((prim => prim)(true)), %loc_LOC());
    Test_utils.eq("None", J.decodeNull((prim => prim)([])), %loc_LOC());
    Test_utils.eq({TAG: "Some", _0: null}, J.decodeNull(null()), %loc_LOC());
    Test_utils.eq("None", J.decodeNull((prim => prim)(()("()"))), %loc_LOC());
    return Test_utils.eq("None", J.decodeNull((prim => prim)(1.23)), %loc_LOC());
  }, "JSON decodeNull");
  return test()(_arg0 => {
    let id = _arg0 => J.deserializeUnsafe(J.serializeExn(obj));
    let idtest = obj => Test_utils.eq(id(obj), obj, %loc_LOC());
    idtest("None");
    idtest({TAG: "::", _0: ["None", "None", "None"], _1: "[]"});
    idtest(Belt.List.makeBy(i => %equal()(0, %mod()(2, i)) ? "None" : {TAG: "Some", _0: 1}, 500));
    return idtest(Belt.Array.makeBy(i => %equal()(0, %mod()(2, i)) ? "None" : {TAG: "Some", _0: 1}, 500));
  }, "JSON serialize/deserialize identity");
}, %loc_MODULE());