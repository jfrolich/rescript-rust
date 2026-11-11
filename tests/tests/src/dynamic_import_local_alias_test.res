// A dynamic import of a local alias of a file module imports that file
module Old = List

let length = async () => {
  module N = await Old
  N.length(list{1, 2})
}
