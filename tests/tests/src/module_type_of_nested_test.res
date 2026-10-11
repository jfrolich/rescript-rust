// The module type of a dynamically imported unit keeps its raw signature:
// nested modules' members refer to each other locally (`chunk`, not
// `WritableStream.chunk`).
let import = async () => {
  module Module = await Module_type_of_nested_types
  Module.version
}
