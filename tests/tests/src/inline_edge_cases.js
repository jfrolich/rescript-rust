let test4 = n => n + 5;

let test3;

test3 = n => n === 0 ? test4(n) + 4 : test3(n - 1);

let test2;

test2 = n => n === 0 ? test3(n) + 3 : test2(n - 1);

let test1;

test1 = n => n === 0 ? test2(n) + 2 : test1(n - 1);

let test0;

test0 = n => n === 0 ? test1(n) : test0(n - 1);

let v = test0(10);

let u = test0(10) + 2;