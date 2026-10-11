type decoder
type bytes
type blob

type decoderOptions = {
  fatal: bool,
  ignoreBOM: bool,
}

let makeDecoder: unit => decoder = %raw(`() => new TextDecoder()`)
let makeDecoderWithLabel: string => decoder = %raw(`(label) => new TextDecoder(label)`)
let makeDecoderWithOptions: (
  string,
  decoderOptions,
) => decoder = %raw(`(label, options) => new TextDecoder(label, options)`)

@send external decodeUnsafe: (decoder, bytes) => string = "decode"

let decode = (decoder, bytes) => {
  try {
    Ok(decodeUnsafe(decoder, bytes))
  } catch {
  | error => Error(error)
  }
}

let bytesToUtf8: bytes => string = %raw(`
function bytesToUtf8(bytes) {
  return new TextDecoder("utf-8").decode(bytes);
}
`)

let mode: array<int> => array<int> = %raw(`
function mode(values) {
  var counter = {};
  var output = [];
  var max = 0;
  for (var index in values) {
    if (!(values[index] in counter)) {
      counter[values[index]] = 0;
    }
    counter[values[index]]++;
    if (counter[values[index]] == max) {
      output.push(values[index]);
    } else if (counter[values[index]] > max) {
      max = counter[values[index]];
      output = [values[index]];
    }
  }
  return output;
}
`)

let blobToDataURL: blob => Promise.t<string> = %raw(`
function blobToDataURL(blob) {
  return new Promise((resolve, reject) => {
    var reader = new globalThis.FileReader();
    reader.onload = function(event) {
      resolve(event.target.result);
    };
    reader.onerror = reject;
    reader.readAsDataURL(blob);
  });
}
`)

let output = (
  makeDecoder,
  makeDecoderWithLabel,
  makeDecoderWithOptions,
  decode,
  bytesToUtf8,
  mode,
  blobToDataURL,
)
