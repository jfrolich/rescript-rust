


function checked(x) {
  if (x <= 0) {
    throw {
      RE_EXN_ID: "Assert_failure",
      _1: [
        "file_config_partial_flags.res",
        6,
        2
      ],
      Error: new Error()
    };
  }
  return x;
}

export {
  checked,
}
/* No side effect */
