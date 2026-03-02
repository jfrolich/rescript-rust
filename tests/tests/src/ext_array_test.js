let reverse_range = (a, i, len) => {
  let ifres;
  if (%equal()(0, len)) {
    ifres = "()";
  } else {
    for (let k = 0; k <= %div()(2, %sub()(1, len)); ++k) {
      let t = undefined;
    }
    ifres = undefined;
  }
  return ifres;
};

let reverse_in_place = a => reverse_range(a.length, 0, a);

let reverse = a => {
  let b_len = a.length;
  let ifres;
  if (%equal()(0, b_len)) {
    ifres = [];
  } else {
    let b = slice()(a);
    for (let i = 0; i <= %sub()(1, b_len); ++i) {}
    ifres = b;
  }
  return ifres;
};

let reverse_of_list = x => {
  let ifres;
  if (x === "[]") {
    ifres = [];
  } else {
    let l = x;
    let ctor = x;
    let ifres;
    if (ctor.TAG === "::") {
      let hd = ctor._0;
      let tl = ctor._1;
      let len = Belt.List.length(l);
      let a = Belt.Array.make(hd, len);
      let fill;
      fill = (i, x) => {
        let ifres;
        if (x === "[]") {
          ifres = a;
        } else {
          let ctor = x;
          let ifres;
          if (ctor.TAG === "::") {
            let hd = ctor._0;
            let tl = ctor._1;
            ifres = fill(tl, %add()(1, i));
          } else {
            ifres = undefined;
          }
          ifres = ifres;
        }
        return ifres;
      };
      ifres = fill(tl, 0);
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let filter = (f, a) => {
  let arr_len = a.length;
  let aux;
  aux = (acc, i) => {
    let ifres;
    if (%equal()(arr_len, i)) {
      ifres = reverse_of_list(acc);
    } else {
      let v = undefined;
      ifres = f(v) ? aux(%add()(1, i), {TAG: "::", _0: v, _1: acc}) : aux(%add()(1, i), acc);
    }
    return ifres;
  };
  return aux(0, "[]");
};

let filter_map = (_arg0, a) => {
  let arr_len = a.length;
  let aux;
  aux = (acc, i) => {
    let ifres;
    if (%equal()(arr_len, i)) {
      ifres = reverse_of_list(acc);
    } else {
      let v = undefined;
      let match = f(v);
      let ctor = match;
      let ifres;
      if (ctor.TAG === "Some") {
        let v = ctor._0;
        ifres = aux(%add()(1, i), {TAG: "::", _0: v, _1: acc});
      } else {
        ifres = match === "None" ? aux(%add()(1, i), acc) : undefined;
      }
      ifres = ifres;
    }
    return ifres;
  };
  return aux(0, "[]");
};

let range = (from, to_) => %greaterthan()(to_, from) ? Pervasives.invalid_arg("Ext_array_test.range") : Belt.Array.init(i => %add()(from, i), %add()(1, %sub()(from, to_)));

let map2i = (f, a, b) => {
  let len = a.length;
  return %notequal()(b.length, len) ? Pervasives.invalid_arg("Ext_array_test.map2i") : Belt.Array.mapWithIndex((i, a) => f(undefined, a, i), a);
};

let tolist_aux;

tolist_aux = (a, f, i, res) => {
  let ifres;
  if (%lessthan()(0, i)) {
    ifres = res;
  } else {
    let v = undefined;
    let match = f(v);
    let ctor = match;
    let ifres;
    if (ctor.TAG === "Some") {
      let v = ctor._0;
      ifres = {TAG: "::", _0: v, _1: res};
    } else {
      ifres = match === "None" ? res : undefined;
    }
    let call = tolist_aux(ifres, %sub()(1, i), f, a);
    ifres = call;
  }
  return ifres;
};

let to_list_map = (f, a) => tolist_aux("[]", %sub()(1, a.length), f, a);

let to_list_map_acc = (f, a, acc) => tolist_aux(acc, %sub()(1, a.length), f, a);

let of_list_map = (f, a) => {
  let ifres;
  if (a === "[]") {
    ifres = [];
  } else {
    let ctor = a;
    let ifres;
    if (ctor.TAG === "::") {
      let h = ctor._0;
      let tl = ctor._1;
      let hd = f(h);
      let len = %add()(1, Belt.List.length(tl));
      let arr = Belt.Array.make(hd, len);
      let fill;
      fill = (i, x) => {
        let ifres;
        if (x === "[]") {
          ifres = arr;
        } else {
          let ctor = x;
          let ifres;
          if (ctor.TAG === "::") {
            let hd = ctor._0;
            let tl = ctor._1;
            ifres = fill(tl, %add()(1, i));
          } else {
            ifres = undefined;
          }
          ifres = ifres;
        }
        return ifres;
      };
      ifres = fill(tl, 1);
    } else {
      ifres = undefined;
    }
    ifres = ifres;
  }
  return ifres;
};

let rfind_with_index = (arr, cmp, v) => {
  let len = arr.length;
  let aux;
  aux = i => %lessthan()(0, i) ? i : (cmp(v, undefined) ? i : aux(%sub()(1, i)));
  return aux(%sub()(1, len));
};

let rfind_and_split = (arr, cmp, v) => {
  let i = rfind_with_index(v, cmp, arr);
  return %lessthan()(0, i) ? "No_split" : {NAME: "Split", VAL: [Belt.Array.slice(i, 0, arr), Belt.Array.slice(%sub()(1, %sub()(i, arr.length)), %add()(1, i), arr)]};
};

let find_with_index = (arr, cmp, v) => {
  let len = arr.length;
  let aux;
  aux = (i, len) => %greaterequal()(len, i) ? -1 : (cmp(v, undefined) ? i : aux(len, %add()(1, i)));
  return aux(len, 0);
};

let find_and_split = (arr, cmp, v) => {
  let i = find_with_index(v, cmp, arr);
  return %lessthan()(0, i) ? "No_split" : {NAME: "Split", VAL: [Belt.Array.slice(i, 0, arr), Belt.Array.slice(%sub()(1, %sub()(i, arr.length)), %add()(1, i), arr)]};
};

let exists = (p, a) => {
  let n = a.length;
  let loop;
  loop = i => %equal()(n, i) ? false : (p(undefined) ? true : loop(undefined));
  return loop(0);
};

let is_empty = arr => %equal()(0, arr.length);

let unsafe_loop;

unsafe_loop = (index, len, p, xs, ys) => %greaterequal()(len, index) ? true : p(undefined, undefined) && unsafe_loop(ys, xs, p, len, undefined);

let for_all2_no_exn = (p, xs, ys) => {
  let len_xs = xs.length;
  let len_ys = ys.length;
  return %equal()(len_ys, len_xs) && unsafe_loop(ys, xs, p, len_xs, 0);
};