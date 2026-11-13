@val external later: (unit => int) => unit = "setTimeout"

let rec loop = (i, acc, fs) =>
  if i == 0 {
    acc
  } else {
    later(() => i + acc)
    loop(i - 1, acc + i, fs)
  }

let rec collect = (n, callbacks) =>
  if n == 0 {
    callbacks
  } else {
    collect(n - 1, Array.concat([() => n], callbacks))
  }
