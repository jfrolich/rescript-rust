let inOrder = _arg0 => {
  let current = %makeref()(v);
  let s = S.make("()");
  let q = Q.make("()");
  while (current.contents !== undefined) {
    let v = (prim => prim)(current.contents);
    S.push(v, s);
    %refset()(leftGet(v), current);
  };
  while (!S.isEmpty(s)) {
    %refset()(S.popUndefined(s), current);
    let v = (prim => prim)(current.contents);
    Q.add(valueGet(v), q);
    %refset()(rightGet(v), current);
    while (current.contents !== undefined) {
      let v = (prim => prim)(current.contents);
      S.push(v, s);
      %refset()(leftGet(v), current);
    };
  };
  return Q.toArray(q);
};

let inOrder3 = _arg0 => {
  let current = %makeref()(v);
  let s = S.make("()");
  let q = Q.make("()");
  while (current.contents !== undefined) {
    let v = (prim => prim)(current.contents);
    S.push(v, s);
    %refset()(leftGet(v), current);
  };
  S.dynamicPopIter(popped => {
    Q.add(valueGet(popped), q);
    let current = %makeref()(rightGet(popped));
    while (current.contents !== undefined) {
      let v = (prim => prim)(current.contents);
      S.push(v, s);
      %refset()(leftGet(v), current);
    };
    
  }, s);
  return Q.toArray(q);
};

let inOrder2 = _arg0 => {
  let todo = %makeref()(true);
  let cursor = %makeref()(v);
  let s = S.make("()");
  let q = Q.make("()");
  while (todo.contents) {
    let ifres;
    if (cursor.contents !== undefined) {
      let v = (prim => prim)(cursor.contents);
      S.push(v, s);
      ifres = %refset()(leftGet(v), cursor);
    } else {
      let ifres;
      if (!S.isEmpty(s)) {
        %refset()(S.popUndefined(s), cursor);
        let current = (prim => prim)(cursor.contents);
        Q.add(valueGet(current), q);
        ifres = %refset()(rightGet(current), cursor);
      } else {
        ifres = %refset()(false, todo);
      }
      ifres = ifres;
    }
    
  };
  
};

let n = (l, r, a) => node(Js.Undefined.fromOption(r), Js.Undefined.fromOption(l), a);

let test1 = n(1, {TAG: "Some", _0: n(3, "None", "None")}, {TAG: "Some", _0: n(2, {TAG: "Some", _0: n(5, "None", "None")}, {TAG: "Some", _0: n(4, "None", "None")})});

let pushAllLeft = (st1, s1) => {
  let current = %makeref()(st1);
  while (current.contents !== undefined) {
    let v = (prim => prim)(current.contents);
    S.push(v, s1);
    %refset()(leftGet(v), current);
  };
  
};

let test2 = n(3, "None", {TAG: "Some", _0: n(1, "None", {TAG: "Some", _0: n(5, "None", {TAG: "Some", _0: n(2, "None", {TAG: "Some", _0: n(4, "None", "None")})})})});

let test3 = n(1, {TAG: "Some", _0: n(3, "None", "None")}, {TAG: "Some", _0: n(5, "None", {TAG: "Some", _0: n(2, "None", {TAG: "Some", _0: n(4, "None", "None")})})});

describe()(_arg0 => test()(_arg0 => {
  Test_utils.eq([4, 2, 5, 1, 3], inOrder((prim => prim)(test1)), %loc_LOC());
  return Test_utils.eq([4, 2, 5, 1, 3], inOrder3((prim => prim)(test1)), %loc_LOC());
}, "tree in-order traversal"), %loc_MODULE());