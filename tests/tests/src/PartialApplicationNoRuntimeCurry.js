let add = x => ((y, z) => %add()(z, %add()(y, x)));

let f = u => {
  let f = add(u);
  return f(1);
};

let add = (a, b) => %add()(b, a);

let add5 = add(5);