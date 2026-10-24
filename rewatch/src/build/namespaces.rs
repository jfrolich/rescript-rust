use crate::build::packages;
use ahash::AHashSet;
use anyhow::{Result, anyhow};
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
// Namespaces work like the following: The build system will generate a file
// called `MyModule.mlmap` which contains all modules that are in the namespace
//
// Not sure what the first line of this file is, but the next lines are names of
// the modules in the namespace you can call bsc with this file, and it will
// produce compiler assets for this file basically a module with all aliases.
// Given that this is just aliases, it doesn not need to create a mjs file.
//
// Internal modules are not accessible with the following trick, they are
// compiled to a module name such as `MyModule-MyNameSpace`.  A dash in a module
// name is not possible to make in a source file, but it's possible when
// constructing the AST, so these modules are hidden from compilation.
// in the top namespace however, we alias with the proper names

pub fn gen_mlmap(
    package: &packages::Package,
    namespace: &str,
    depending_modules: &AHashSet<String>,
) -> Result<PathBuf> {
    let build_path_abs = package.get_build_path();
    // we don't really need to create a digest, because we track if we need to
    // recompile in a different way but we need to put it in the file for it to
    // be readable.

    let path = build_path_abs.join(format!("{namespace}.mlmap"));
    let mut modules: Vec<&String> = depending_modules.iter().collect();
    modules.sort();
    let mut contents = String::from("randjbuildsystem\n");
    for module in modules {
        contents.push_str(module);
        contents.push('\n');
    }
    let mut file =
        File::create(&path).map_err(|e| anyhow!("Unable to create mlmap {}: {e}", path.display()))?;
    file.write_all(contents.as_bytes())
        .map_err(|e| anyhow!("Unable to write mlmap {}: {e}", path.display()))?;

    Ok(path)
}
