//! One TypeScript program per importing ReScript file.
//!
//! The program has a single root: a virtual TypeScript file placed next to the
//! ReScript file, holding one `import * as` per module the ReScript file
//! imports from. TypeScript's own module resolution then decides what each
//! specifier means (relative files, `node_modules`, `paths`, declaration
//! files), exactly as it would for a TypeScript file in that directory.
//!
//! Only parsing and binding happen here. Nothing is type checked until the
//! converter asks the checker for the type of one export.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::SystemTime;

use tsrs_ast::{Node, SourceFile};
use tsrs_compiler::{Program, ProgramOptions, new_compiler_host, new_program};
use tsrs_core::{CompilerOptions, P, Tristate, tspath};
use tsrs_tsoptions::{self as tsoptions, ParseConfigHost};
use tsrs_vfs::{Entries, FS, FileInfo, FileMode, bundled::embed as bundled, osvfs, vfstest};

/// Where TypeScript sources are read from.
#[derive(Clone, Debug)]
pub enum Files {
    /// The real file system.
    Os,
    /// Absolute path and content of every file (tests, the playground).
    Memory(Vec<(String, String)>),
}

/// A file system that adds files to another one without writing them.
struct Overlay {
    base: Arc<dyn FS>,
    files: HashMap<String, String>,
}

impl FS for Overlay {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.base.use_case_sensitive_file_names()
    }
    fn file_exists(&self, path: &str) -> bool {
        self.files.contains_key(path) || self.base.file_exists(path)
    }
    fn read_file(&self, path: &str) -> Option<String> {
        match self.files.get(path) {
            Some(text) => Some(text.clone()),
            None => self.base.read_file(path),
        }
    }
    fn write_file(&self, path: &str, data: &str) -> Result<(), String> {
        self.base.write_file(path, data)
    }
    fn append_file(&self, path: &str, data: &str) -> Result<(), String> {
        self.base.append_file(path, data)
    }
    fn remove(&self, path: &str) -> Result<(), String> {
        self.base.remove(path)
    }
    fn chtimes(&self, path: &str, a_time: SystemTime, m_time: SystemTime) -> Result<(), String> {
        self.base.chtimes(path, a_time, m_time)
    }
    fn directory_exists(&self, path: &str) -> bool {
        self.base.directory_exists(path)
    }
    fn get_accessible_entries(&self, path: &str) -> Entries {
        let mut entries = self.base.get_accessible_entries(path);
        for file in self.files.keys() {
            if tspath::get_directory_path(file) == path {
                let name = tspath::get_base_file_name(file);
                if !entries.files.contains(&name) {
                    entries.files.push(name);
                }
            }
        }
        entries
    }
    fn stat(&self, path: &str) -> Option<FileInfo> {
        match self.files.get(path) {
            Some(text) => Some(FileInfo {
                name: tspath::get_base_file_name(path),
                size: text.len() as i64,
                mode: FileMode::None,
                mod_time: None,
            }),
            None => self.base.stat(path),
        }
    }
    fn realpath(&self, path: &str) -> String {
        if self.files.contains_key(path) { path.to_string() } else { self.base.realpath(path) }
    }
}

struct ConfigHost {
    fs: Arc<dyn FS>,
    cwd: String,
}

impl ParseConfigHost for ConfigHost {
    fn fs(&self) -> &dyn FS {
        &*self.fs
    }
    fn get_current_directory(&self) -> &str {
        &self.cwd
    }
}

/// A parsed and bound program whose only root imports the requested modules.
pub(crate) struct Session {
    pub program: &'static Program,
    /// The virtual root file.
    pub root: P<SourceFile>,
    /// The module specifier node of each requested module, in request order.
    pub specifiers: Vec<P<Node>>,
    /// The `tsconfig.json` whose compiler options apply, when one was found.
    pub tsconfig: Option<String>,
}

/// The options that hold whatever the project's `tsconfig.json` says: the
/// program is never emitted, and `%ts("./a.ts")` may name a `.ts` file.
fn forced_options() -> CompilerOptions {
    CompilerOptions {
        no_emit: Tristate::True,
        allow_importing_ts_extensions: Tristate::True,
        skip_lib_check: Tristate::True,
        ..CompilerOptions::default()
    }
}

/// Options for a directory with no `tsconfig.json`.
const DEFAULT_ARGS: &[&str] = &[
    "--strict",
    "--target",
    "esnext",
    "--module",
    "esnext",
    "--moduleResolution",
    "bundler",
    "--allowImportingTsExtensions",
    "--noEmit",
    "--skipLibCheck",
];

fn nearest_tsconfig(fs: &dyn FS, dir: &str) -> Option<String> {
    let mut dir = dir.to_string();
    loop {
        let candidate = tspath::combine_paths(&dir, &["tsconfig.json"]);
        if fs.file_exists(&candidate) {
            return Some(candidate);
        }
        let parent = tspath::get_directory_path(&dir);
        if parent == dir || parent.is_empty() {
            return None;
        }
        dir = parent;
    }
}

/// The path of the virtual root for a ReScript file: `/dir/Foo.res` imports
/// through `/dir/Foo.res.ts`.
pub(crate) fn virtual_root_path(importer: &str) -> String {
    format!("{}.ts", tspath::normalize_path(importer))
}

impl Session {
    /// Parses and binds the modules `importer` (an absolute path of a ReScript
    /// file) imports. `modules` are the specifiers as written in `%ts("...")`.
    pub(crate) fn open(files: &Files, importer: &str, modules: &[String]) -> Result<Session, String> {
        let root_path = virtual_root_path(importer);
        let dir = tspath::get_directory_path(&root_path);
        let mut root_text = String::new();
        for (index, module) in modules.iter().enumerate() {
            let quoted = crate::model::string_literal(module);
            root_text.push_str(&format!("import * as m{index} from {quoted};\n"));
        }
        let names: Vec<String> = (0..modules.len()).map(|index| format!("m{index}")).collect();
        root_text.push_str(&format!("export {{ {} }};\n", names.join(", ")));

        let base: Arc<dyn FS> = match files {
            Files::Os => Arc::new(bundled::wrap_fs(osvfs::fs())),
            Files::Memory(entries) => Arc::new(bundled::wrap_fs(vfstest::from_map(
                entries.iter().map(|(path, text)| (path.as_str(), text.as_str())),
                true,
            ))),
        };
        let fs: Arc<dyn FS> = Arc::new(Overlay {
            base,
            files: HashMap::from([(root_path.clone(), root_text)]),
        });

        // The parsed command line keeps what it read for the life of the
        // program, and tsrs programs are never freed.
        let host: &'static ConfigHost =
            Box::leak(Box::new(ConfigHost { fs: Arc::clone(&fs), cwd: dir.clone() }));
        let tsconfig = nearest_tsconfig(&*fs, &dir);
        let config = match &tsconfig {
            Some(path) => {
                let forced = forced_options();
                let (config, errors) = tsoptions::get_parsed_command_line_of_config_file(
                    path,
                    Some(&forced),
                    None,
                    host,
                    None,
                );
                match config {
                    Some(config) => config.with_file_names(vec![root_path.clone()]),
                    None => {
                        return Err(format!(
                            "{path} could not be read ({} configuration errors)",
                            errors.len()
                        ));
                    }
                }
            }
            None => {
                let mut args: Vec<String> = DEFAULT_ARGS.iter().map(|arg| (*arg).to_string()).collect();
                args.push(root_path.clone());
                tsoptions::parse_command_line(&args, host)
            }
        };

        let compiler_host = new_compiler_host(&dir, fs, &bundled::lib_path(), None, None, None);
        let mut options = ProgramOptions::new(P::new(config), compiler_host);
        options.single_threaded = Tristate::True;
        let program = new_program(options);
        let Some(root) = program.get_source_file(&root_path) else {
            return Err(format!("the import root {root_path} did not load"));
        };
        let specifiers = root.imports().to_vec();
        if specifiers.len() != modules.len() {
            return Err(format!(
                "expected {} imports in {root_path}, found {}",
                modules.len(),
                specifiers.len()
            ));
        }
        Ok(Session { program, root, specifiers, tsconfig })
    }
}
