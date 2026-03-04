let r = %makeref()(0);

for (let k = 1; k <= 10; ++k) {
  for (let i = 1; i <= 10; ++i) {
    let tuple = %equal()(0, %mod()(2, i)) ? [1, %mul()(2, i)] : [2, %mul()(3, i)];
    let x = tuple[0];
    let y = tuple[1];
    %refset()(%add()(y, %mul()(x, r.contents)), r);
  }
}

let ifres;

if (undefined === "()") {
  ifres = undefined;
} else {
  throw "Match_failure";
  ifres = undefined;
}

