


function div(a, b) {
  return a / b | 0;
}

function rem(a, b) {
  return a % b;
}

function bigDiv(a, b) {
  return a / b;
}

function bigRem(a, b) {
  return a % b;
}

function checked(x) {
  return x;
}

export {
  div,
  rem,
  bigDiv,
  bigRem,
  checked,
}
/* No side effect */
