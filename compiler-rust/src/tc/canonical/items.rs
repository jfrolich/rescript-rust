//! The `== items` section: per item, what the type printer leaves out
//! (types/canonical_sig.rs `Canonical`), read from segment rows. The
//! signature tree and every type are walked with explicit stacks.

use std::fmt::Write as _;

use super::view::{Desc, Graph, N};
use super::text::LongidentStyle;
use crate::tc::graph::{GENERIC, NONE};
use crate::tc::segment::{
    ConstructorArgumentsRow, DeclarationKind, ExtensionStatus, ItemStatus,
    ModuleTypeRow, PathRow, Range, RecStatus, RecordRepresentationRow, RowFieldKind, ShapeRow,
    SignatureKind,
};

/// `Pdot` position of a path that has none (types/path.rs `NOPOS`).
const NOPOS: i32 = -1;

/// Eight bytes per populated dense-table slot; epochs avoid a clearing walk.
#[derive(Clone, Copy, Default)]
struct NodeNumber {
    epoch: u32,
    number: u32,
}

/// types/canonical_sig.rs `NodeNumbers`, over the dense node range.
#[derive(Default)]
struct NodeNumbers {
    table: Vec<NodeNumber>,
    epoch: u32,
    variables: u32,
    structures: u32,
}

impl NodeNumbers {
    /// O(1). An item count exceeding u32 is rejected instead of wrapping epochs.
    fn clear(&mut self) {
        self.epoch = self.epoch.checked_add(1).expect("too many signature items");
        self.variables = 0;
        self.structures = 0;
    }

    /// Amortized O(1); table growth costs O(new slots), never hashes a node.
    fn number(&mut self, n: N, variable: bool) -> (u32, bool) {
        let index = n.0 as usize;
        if index >= self.table.len() {
            self.table
                .resize((index + 1).next_power_of_two(), NodeNumber::default());
        }
        let slot = &mut self.table[index];
        if slot.epoch != 0 && slot.epoch == self.epoch {
            return (slot.number, false);
        }
        let next = if variable {
            &mut self.variables
        } else {
            &mut self.structures
        };
        *slot = NodeNumber {
            epoch: self.epoch,
            number: *next,
        };
        *next = next.checked_add(1).expect("too many canonical nodes");
        (slot.number, true)
    }
}

/// Twelve-byte work item; text is in one shared byte pool.
#[derive(Clone, Copy)]
enum PrintTask {
    Type(N),
    Text { start: u32, end: u32 },
}

/// Words of the signature walk.
const WORDS: [&str; 3] = ["result", "generative", "abstract"];

/// One signature walk step. Twelve bytes; text is never owned by a step.
#[derive(Clone, Copy)]
enum Step {
    /// The items of `signatures[sig]`.
    Signature {
        sig: u32,
        components: bool,
    },
    /// Item `index` of `ordered_items`.
    Item {
        index: u32,
        components: bool,
    },
    /// A module type row.
    ModuleType {
        row: u32,
        components: bool,
    },
    /// Close a signature: forget its own items past `in_scope`.
    EndSignature {
        in_scope: u32,
    },
    Word(u8),
    Dedent,
    /// Restore the module prefix to `len` bytes.
    Prefix {
        len: u32,
    },
}

/// One of the unit's own items in scope: its identity key, its name from
/// the unit's top in `names[start..end]`, and the entry it shadows.
#[derive(Clone, Copy)]
struct Own {
    key: u32,
    start: u32,
    end: u32,
    shadowed: u32,
}

/// Where a path starts (types/canonical_sig.rs `PathRoot`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum PathRoot {
    Unit,
    Own,
    Other,
}

/// Path walk step for writing a path without recursion. Eight bytes.
/// `trim` marks the outermost path of a renamed private row type, whose
/// last name drops its `#row` suffix.
#[derive(Clone, Copy)]
enum PathStep {
    Any(u32, bool),
    Own(u32, bool),
    Other(u32, bool),
    /// A string of the pool, trimmed or not.
    Name(u32, bool),
    /// `.`, `(` or `)`.
    Char(u8),
    Position(i32),
}

/// O(1): `name`, without its last four bytes (`#row`) when `trim`.
fn trimmed(name: &str, trim: bool) -> &str {
    if trim { &name[..name.len() - 4] } else { name }
}

pub(super) struct Items<'g, 's> {
    g: &'g mut Graph<'s>,
    unit_name: u32,
    own: Vec<Own>,
    own_index: Vec<u32>,
    identity: Vec<u32>,
    names: String,
    prefix: String,
    out: String,
    indent: usize,
    numbers: NodeNumbers,
    work: Vec<PrintTask>,
    text: String,
    path_work: Vec<PathStep>,
}

impl<'g, 's> Items<'g, 's> {
    pub fn new(g: &'g mut Graph<'s>, out: String) -> Self {
        let unit_name = g.v.p.unit.map_or(NONE, |unit| unit.name);
        // Stamps are sparse and renamed rows can share a stamp. Sort once,
        // then all lexical-scope lookups use dense identifier indices.
        let mut keys: Vec<_> =
            g.v.p
                .identifiers
                .iter()
                .enumerate()
                .map(|(id, row)| {
                    let key = if row.stamp == 0 {
                        (1u64 << 32) | u64::from(row.name)
                    } else {
                        u64::from(row.stamp as u32)
                    };
                    (key, id as u32)
                })
                .collect();
        keys.sort_unstable();
        let mut identity = vec![NONE; keys.len()];
        let mut previous = None;
        let mut representative = NONE;
        for (key, id) in keys {
            if previous != Some(key) {
                representative = id;
                previous = Some(key);
            }
            identity[id as usize] = representative;
        }
        Items {
            g,
            unit_name,
            own: Vec::new(),
            own_index: vec![NONE; identity.len()],
            identity,
            names: String::new(),
            prefix: String::new(),
            out,
            indent: 0,
            numbers: NodeNumbers::default(),
            work: Vec::new(),
            text: String::new(),
            path_work: Vec::new(),
        }
    }

    /// O(signature items + their declaration metadata + type nodes printed),
    /// one explicit step stack whatever the module nesting.
    pub fn run(mut self, top: u32) -> String {
        let mut steps = vec![Step::Signature {
            sig: top,
            components: true,
        }];
        while let Some(step) = steps.pop() {
            match step {
                Step::Signature { sig, components } => {
                    let range = self.g.v.p.signatures[sig as usize];
                    let in_scope = self.own.len() as u32;
                    if components {
                        for index in range.start..range.start + range.len {
                            let item = self.g.v.p.ordered_items[index as usize];
                            if matches!(
                                item.kind,
                                SignatureKind::Type
                                    | SignatureKind::Module
                                    | SignatureKind::ModuleType
                            ) {
                                self.add_own(item.ident);
                            }
                        }
                    }
                    steps.push(Step::EndSignature { in_scope });
                    for index in (range.start..range.start + range.len).rev() {
                        steps.push(Step::Item { index, components });
                    }
                }
                Step::EndSignature { in_scope } => self.truncate_own(in_scope),
                Step::Item { index, components } => self.item(index, components, &mut steps),
                Step::ModuleType { row, components } => {
                    self.module_type(row, components, &mut steps)
                }
                Step::Word(word) => self.line(WORDS[word as usize]),
                Step::Dedent => self.indent -= 1,
                Step::Prefix { len } => self.prefix.truncate(len as usize),
            }
        }
        self.out
    }

    /// O(1): the dense representative of this identifier's identity.
    fn key(&self, ident: u32) -> u32 {
        self.identity[ident as usize]
    }

    /// Amortized O(name length).
    fn add_own(&mut self, ident: u32) {
        let key = self.key(ident);
        let start = self.names.len() as u32;
        self.names.push_str(&self.prefix);
        self.names
            .push_str(self.g.v.str(self.g.v.ident(ident).name));
        let shadowed = self.own_index[key as usize];
        let index = self.own.len() as u32;
        self.own.push(Own {
            key,
            start,
            end: self.names.len() as u32,
            shadowed,
        });
        self.own_index[key as usize] = index;
    }

    /// O(entries removed).
    fn truncate_own(&mut self, len: u32) {
        while self.own.len() as u32 > len {
            let own = self.own.pop().expect("an own item");
            self.own_index[own.key as usize] = own.shadowed;
            self.names.truncate(own.start as usize);
        }
    }

    /// O(text).
    fn line(&mut self, text: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(text);
        self.out.push('\n');
    }

    /// O(the item's metadata and types); a nested module type is queued.
    fn item(&mut self, index: u32, components: bool, steps: &mut Vec<Step>) {
        let item = self.g.v.p.ordered_items[index as usize];
        // Sharing is recorded within an item, never across items.
        self.numbers.clear();
        let name = if item.ident == NONE {
            ""
        } else {
            self.g.v.str(self.g.v.ident(item.ident).name)
        };
        match item.kind {
            SignatureKind::Value => self.value(name, item.declaration),
            SignatureKind::Type => {
                let status = rec_status(item.status);
                self.line(&format!("type {name} {status}"));
                self.indent += 1;
                self.type_declaration(item.declaration);
                self.indent -= 1;
            }
            SignatureKind::Extension => {
                let status = match item.status {
                    ItemStatus::Extension(ExtensionStatus::First) => "TextFirst",
                    ItemStatus::Extension(ExtensionStatus::Next) => "TextNext",
                    _ => "TextException",
                };
                self.line(&format!("typext {name} {status}"));
                self.indent += 1;
                self.extension(item.declaration);
                self.indent -= 1;
            }
            SignatureKind::Module => {
                let status = rec_status(item.status);
                self.line(&format!("module {name} {status}"));
                self.indent += 1;
                let module = self.g.v.p.modules[item.declaration as usize];
                self.attributes(module.attributes);
                let len = self.prefix.len() as u32;
                if components {
                    self.prefix.push_str(name);
                    self.prefix.push('.');
                }
                steps.push(Step::Dedent);
                steps.push(Step::Prefix { len });
                steps.push(Step::ModuleType {
                    row: module.module_type,
                    components,
                });
            }
            SignatureKind::ModuleType => {
                self.line(&format!("modtype {name}"));
                self.indent += 1;
                let module = self.g.v.p.modules[item.declaration as usize];
                self.attributes(module.attributes);
                steps.push(Step::Dedent);
                if module.module_type == NONE {
                    steps.push(Step::Word(2));
                } else {
                    steps.push(Step::ModuleType {
                        row: module.module_type,
                        components: false,
                    });
                }
            }
            SignatureKind::Class => self.line("class"),
            SignatureKind::ClassType => self.line("classtype"),
        }
    }

    /// O(path); a signature or functor is queued.
    fn module_type(&mut self, row: u32, components: bool, steps: &mut Vec<Step>) {
        match self.g.v.p.module_types[row as usize] {
            ModuleTypeRow::Ident(path) => {
                let path = self.path_text(path);
                self.line(&format!("ident {path}"));
            }
            ModuleTypeRow::Alias { path, present } => {
                let path = self.path_text(path);
                let presence = if present { "MtaPresent" } else { "MtaAbsent" };
                self.line(&format!("alias {presence} {path}"));
            }
            ModuleTypeRow::Signature(sig) => {
                self.line("sig");
                self.indent += 1;
                // Each nested item numbers its nodes afresh, as the old
                // printer's swapped-out numbering does.
                steps.push(Step::Dedent);
                steps.push(Step::Signature { sig, components });
            }
            ModuleTypeRow::Functor {
                parameter,
                parameter_type,
                result,
            } => {
                let name = self.g.v.str(self.g.v.ident(parameter).name);
                self.line(&format!("functor {name}"));
                self.indent += 1;
                steps.push(Step::Dedent);
                steps.push(Step::ModuleType {
                    row: result,
                    components: false,
                });
                steps.push(Step::Word(0));
                if parameter_type == NONE {
                    steps.push(Step::Word(1));
                } else {
                    steps.push(Step::ModuleType {
                        row: parameter_type,
                        components: false,
                    });
                }
            }
        }
    }

    /// O(the value's type and metadata).
    fn value(&mut self, name: &str, row: u32) {
        let value = self.g.v.p.values[row as usize];
        let ty = self.root_text(value.ty);
        self.line(&format!("value {name}: {ty}"));
        self.indent += 1;
        if value.primitive != NONE {
            let v = &self.g.v;
            let prim = v.p.primitives[value.primitive as usize];
            let mut text = String::new();
            let _ = write!(
                text,
                "prim {:?} arity={} native_float={} from_constructor={} ",
                v.str(prim.name),
                prim.arity,
                prim.native_float,
                prim.from_constructor
            );
            v.prim_kind_debug(&mut text, prim.kind);
            self.line(&text);
        }
        self.attributes(value.attributes);
        self.indent -= 1;
    }

    /// O(the declaration's metadata and types).
    fn type_declaration(&mut self, index: u32) {
        let decl = self.g.v.seg.type_declarations[index as usize];
        let details = self.g.v.p.type_details[index as usize];
        let params = self.roots_text(details.parameter_roots);
        self.line(&format!(
            "params [{params}] arity={} {} immediate={} {}",
            decl.arity,
            if decl.flags & 1 != 0 {
                "Private"
            } else {
                "Public"
            },
            decl.flags & 2 != 0,
            if decl.flags & 4 != 0 {
                "Unboxed"
            } else {
                "Boxed"
            },
        ));
        let mut variance = String::from("variance [");
        for i in 0..details.variance.len {
            if i > 0 {
                variance.push_str(", ");
            }
            let bits = self.g.v.p.variance[(details.variance.start + i) as usize];
            let _ = write!(variance, "Variance({bits})");
        }
        variance.push(']');
        self.line(&variance);
        match self.g.v.p.shapes[details.shape as usize] {
            ShapeRow::Unstated => {}
            ShapeRow::NeverUndefined => self.line("shape never-undefined"),
            ShapeRow::Recognized(block_type) => {
                let mut text = String::from("shape ");
                self.g.v.block_type_text(&mut text, block_type);
                self.line(&text);
            }
        }
        if decl.manifest != NONE {
            let manifest = self.root_text(decl.manifest);
            self.line(&format!("manifest {manifest}"));
        }
        self.attributes(details.attributes);
        match decl.kind {
            DeclarationKind::Abstract => self.line("abstract"),
            DeclarationKind::Open => self.line("open"),
            DeclarationKind::Record => {
                let mut text = String::from("record ");
                self.record_representation(&mut text, details.representation);
                self.line(&text);
                // A record's members are its labels, in one contiguous range.
                let labels = if decl.member_len == 0 {
                    Range::default()
                } else {
                    let first = self.g.v.seg.members[decl.members as usize].args;
                    Range {
                        start: first,
                        len: decl.member_len,
                    }
                };
                self.labels(labels);
            }
            DeclarationKind::Variant => {
                let mut text = String::from("variant ");
                self.g.v.layout_text(&mut text, details.representation);
                self.line(&text);
                self.indent += 1;
                for i in 0..decl.member_len {
                    let member = self.g.v.seg.members[(decl.members + i) as usize];
                    let constructor = self.g.v.p.constructors[member.args as usize];
                    let res = if constructor.result == NONE {
                        String::new()
                    } else {
                        format!(": {}", self.root_text(constructor.result))
                    };
                    let v = &self.g.v;
                    let mut text = format!(
                        "constructor {} tag=",
                        v.str(v.ident(constructor.ident).name)
                    );
                    v.opt_literal_debug(&mut text, constructor.runtime_tag);
                    text.push_str(&res);
                    self.line(&text);
                    self.indent += 1;
                    self.attributes(constructor.attributes);
                    self.constructor_arguments(constructor.arguments);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
        }
        for i in 0..details.inlined_records.len {
            let inlined = self.g.v.p.inlined_records[(details.inlined_records.start + i) as usize];
            let name = self.g.v.str(inlined.name);
            self.line(&format!("inlined record {name}"));
            self.labels(inlined.labels);
        }
    }

    /// O(1) plus a layout.
    fn record_representation(&self, out: &mut String, row: u32) {
        match self.g.v.p.record_representations[row as usize] {
            RecordRepresentationRow::Regular => out.push_str("RecordRegular"),
            RecordRepresentationRow::Array => out.push_str("RecordArray"),
            RecordRepresentationRow::Unboxed(b) => {
                let _ = write!(out, "RecordUnboxed({b})");
            }
            RecordRepresentationRow::Extension => out.push_str("RecordExtension"),
            RecordRepresentationRow::Inlined {
                name,
                position,
                layout,
            } => {
                let _ = write!(
                    out,
                    "RecordInlined {} position={position} ",
                    self.g.v.str(name)
                );
                self.g.v.layout_text(out, layout);
            }
        }
    }

    /// O(labels and their types).
    fn labels(&mut self, labels: Range) {
        self.indent += 1;
        for i in 0..labels.len {
            let label = self.g.v.p.labels[(labels.start + i) as usize];
            let ty = self.root_text(label.ty);
            let v = &self.g.v;
            let mut text = format!("label {} runtime=", v.str(v.ident(label.ident).name));
            v.opt_string_debug(&mut text, label.runtime_name);
            let _ = write!(
                text,
                " {} optional={}: {ty}",
                if label.mutable {
                    "Mutable"
                } else {
                    "Immutable"
                },
                label.optional
            );
            self.line(&text);
            self.indent += 1;
            self.attributes(label.attributes);
            self.indent -= 1;
        }
        self.indent -= 1;
    }

    /// O(arguments).
    fn constructor_arguments(&mut self, row: u32) {
        match self.g.v.p.constructor_arguments[row as usize] {
            ConstructorArgumentsRow::Tuple(roots) => {
                if roots.len != 0 {
                    let types = self.roots_text(roots);
                    self.line(&format!("args ({types})"));
                }
            }
            ConstructorArgumentsRow::Record(labels) => {
                self.line("args record");
                self.labels(labels);
            }
        }
    }

    /// O(the extension's metadata and types).
    fn extension(&mut self, row: u32) {
        let ext = self.g.v.p.extensions[row as usize];
        let path = self.path_text(ext.path);
        let params = self.roots_text(ext.parameters);
        let ret = if ext.result == NONE {
            String::new()
        } else {
            format!(": {}", self.root_text(ext.result))
        };
        self.line(&format!(
            "of {path} params [{params}] {} exception={}{ret}",
            if ext.private { "Private" } else { "Public" },
            ext.exception
        ));
        self.attributes(ext.attributes);
        self.constructor_arguments(ext.arguments);
    }

    /// O(attributes and payloads).
    fn attributes(&mut self, attributes: Range) {
        for i in 0..attributes.len {
            let attribute = self.g.v.p.attributes[(attributes.start + i) as usize];
            let v = &self.g.v;
            let mut text = format!("@{} ", v.str(attribute.name));
            v.attribute_payload_text(&mut text, attribute.payload);
            self.line(&text);
        }
    }

    /// O(path length): where a path starts. A `Pdot` chain is walked to its
    /// root; an application is another unit's.
    fn path_root(&self, path: u32) -> PathRoot {
        let mut current = path;
        loop {
            match self.g.v.path(current) {
                PathRow::Ident(id) => {
                    let row = self.g.v.ident(id);
                    let unit = row.stamp == 0 && row.name == self.unit_name;
                    let root = if unit {
                        PathRoot::Unit
                    } else if self.own_index[self.key(id) as usize] != NONE {
                        PathRoot::Own
                    } else {
                        PathRoot::Other
                    };
                    return if current != path && root == PathRoot::Unit {
                        PathRoot::Own
                    } else {
                        root
                    };
                }
                PathRow::Dot { parent, .. } => current = parent,
                PathRow::Apply { .. } => {
                    return PathRoot::Other;
                }
            }
        }
    }

    /// O(path length + output): types/canonical_sig.rs `path`.
    fn path_text(&mut self, path: u32) -> String {
        let mut text = String::new();
        self.write_path(&mut text, path, false);
        text
    }

    /// O(path length + output), one explicit stack: types/canonical_sig.rs
    /// `write_path`, `write_own_path` and `write_other_path`. With `trim`
    /// the outermost name drops its `#row` suffix.
    fn write_path(&mut self, out: &mut String, path: u32, trim: bool) {
        let mut work = std::mem::take(&mut self.path_work);
        work.clear();
        work.push(PathStep::Any(path, trim));
        while let Some(step) = work.pop() {
            let v = &self.g.v;
            match step {
                PathStep::Char(c) => out.push(c as char),
                PathStep::Name(name, trim) => out.push_str(trimmed(v.str(name), trim)),
                PathStep::Position(position) => {
                    let _ = write!(out, "@{position}");
                }
                PathStep::Any(p, trim) => match self.path_root(p) {
                    PathRoot::Unit => {}
                    PathRoot::Own => work.push(PathStep::Own(p, trim)),
                    PathRoot::Other => work.push(PathStep::Other(p, trim)),
                },
                PathStep::Own(p, trim) => match v.path(p) {
                    PathRow::Ident(id) => match self.own_index[self.key(id) as usize] {
                        NONE => out.push_str(trimmed(v.str(v.ident(id).name), trim)),
                        index => {
                            let own = self.own[index as usize];
                            let name = &self.names[own.start as usize..own.end as usize];
                            out.push_str(trimmed(name, trim));
                        }
                    },
                    PathRow::Dot { parent, name, .. } => {
                        let unit = matches!(v.path(parent), PathRow::Ident(id)
                            if v.ident(id).stamp == 0 && v.ident(id).name == self.unit_name);
                        work.push(PathStep::Name(name, trim));
                        if !unit {
                            work.push(PathStep::Char(b'.'));
                            work.push(PathStep::Own(parent, false));
                        }
                    }
                    PathRow::Apply { .. } => work.push(PathStep::Other(p, trim)),
                },
                PathStep::Other(p, trim) => match v.path(p) {
                    PathRow::Ident(id) => out.push_str(trimmed(v.str(v.ident(id).name), trim)),
                    PathRow::Dot {
                        parent,
                        name,
                        position,
                    } => {
                        if position != NOPOS {
                            work.push(PathStep::Position(position));
                        }
                        work.push(PathStep::Name(name, trim));
                        work.push(PathStep::Char(b'.'));
                        work.push(PathStep::Other(parent, false));
                    }
                    PathRow::Apply { functor, argument } => {
                        work.push(PathStep::Char(b')'));
                        work.push(PathStep::Any(argument, false));
                        work.push(PathStep::Char(b'('));
                        work.push(PathStep::Any(functor, false));
                    }
                },
            }
        }
        self.path_work = work;
    }

    /// O(the type): the text of root row `root`.
    fn root_text(&mut self, root: u32) -> String {
        let n = self.g.v.root_at(root);
        let mut text = String::new();
        self.write_type(&mut text, n);
        text
    }

    /// O(the types): roots joined with `", "`.
    fn roots_text(&mut self, roots: Range) -> String {
        let mut text = String::new();
        for i in 0..roots.len {
            if i > 0 {
                text.push_str(", ");
            }
            let n = self.g.v.root_at(roots.start + i);
            self.write_type(&mut text, n);
        }
        text
    }

    /// O(nodes + edges + output bytes): types/canonical_sig.rs `write_type`.
    /// One explicit task pool and text pool replace recursion; shared nodes
    /// are expanded once per item. Test builds count each dispatched task.
    pub(super) fn write_type(&mut self, output: &mut String, root: N) {
        let mut work = std::mem::take(&mut self.work);
        let mut text = std::mem::take(&mut self.text);
        work.clear();
        text.clear();
        work.push(PrintTask::Type(root));
        while let Some(task) = work.pop() {
            #[cfg(test)]
            crate::tc::steps::tick();
            let ty = match task {
                PrintTask::Text { start, end } => {
                    output.push_str(&text[start as usize..end as usize]);
                    continue;
                }
                PrintTask::Type(ty) => ty,
            };
            let desc = self.g.desc(ty);
            if let Desc::Var(name) | Desc::Univar(name) = desc {
                let (index, _) = self.numbers.number(ty, true);
                output.push(if matches!(desc, Desc::Var(_)) {
                    '\''
                } else {
                    '!'
                });
                if self.g.level(ty) != GENERIC {
                    output.push('_');
                }
                let _ = write!(output, "{index}");
                if name != NONE {
                    let _ = write!(output, ":{}", self.g.v.str(name));
                }
                continue;
            }
            let (number, fresh) = self.numbers.number(ty, false);
            if !fresh {
                let _ = write!(output, "@{number}");
                continue;
            }
            let _ = write!(output, "&{number}(");
            let first = work.len();
            let mut start = text.len();
            macro_rules! flush {
                () => {{
                    let end = text.len();
                    if end != start {
                        work.push(PrintTask::Text {
                            start: u32::try_from(start).expect("canonical text exceeds u32"),
                            end: u32::try_from(end).expect("canonical text exceeds u32"),
                        });
                    }
                    start = end;
                }};
            }
            macro_rules! child {
                ($ty:expr) => {{
                    let child = $ty;
                    flush!();
                    work.push(PrintTask::Type(child));
                }};
            }
            match desc {
                Desc::Var(_) | Desc::Univar(_) | Desc::Subst(_) => text.push_str("<link>"),
                Desc::Nil => text.push_str("nil"),
                Desc::Arrow { params, ret } => {
                    text.push('(');
                    for i in 0..params.len {
                        if i > 0 {
                            text.push_str(", ");
                        }
                        let (label, typ) = self.g.param(params, i);
                        if label != NONE {
                            text.push(if label & 1 != 0 { '?' } else { '~' });
                            text.push_str(self.g.v.str(label >> 1));
                            text.push(':');
                        }
                        child!(typ);
                    }
                    text.push_str(") => ");
                    child!(ret);
                }
                Desc::Tuple(slots) => {
                    text.push_str("tuple(");
                    for i in 0..slots.len {
                        if i > 0 {
                            text.push_str(", ");
                        }
                        child!(self.g.slot(slots, i));
                    }
                    text.push(')');
                }
                Desc::Constr { path, trim, args } => {
                    self.write_path(&mut text, path, trim);
                    if args.len != 0 {
                        text.push('<');
                        for i in 0..args.len {
                            if i > 0 {
                                text.push_str(", ");
                            }
                            child!(self.g.slot(args, i));
                        }
                        text.push('>');
                    }
                }
                Desc::Object(fields) => {
                    text.push_str("object{");
                    child!(fields);
                    text.push('}');
                }
                Desc::Field {
                    name,
                    mutable,
                    typ,
                    rest,
                } => {
                    let _ = write!(
                        text,
                        "{}[{}]: ",
                        self.g.v.str(name),
                        if mutable { "Mutable" } else { "Immutable" }
                    );
                    child!(typ);
                    text.push_str("; ");
                    child!(rest);
                }
                Desc::Variant => {
                    let row = self.g.row(ty);
                    text.push_str("variant[");
                    for i in 0..row.fields.len {
                        if i > 0 {
                            text.push_str(" | ");
                        }
                        let field = self.g.field(row.fields, i);
                        let _ = write!(text, "#{}", self.g.v.str(field.label));
                        match field.kind {
                            RowFieldKind::Present => {
                                if field.types.len != 0 {
                                    text.push('(');
                                    child!(self.g.ns_at(field.types, 0));
                                    text.push(')');
                                }
                            }
                            RowFieldKind::Either { constant, matched } => {
                                let _ =
                                    write!(text, " either constant={constant} matched={matched} (");
                                for k in 0..field.types.len {
                                    if k > 0 {
                                        text.push_str(", ");
                                    }
                                    child!(self.g.ns_at(field.types, k));
                                }
                                text.push(')');
                            }
                            RowFieldKind::Absent => text.push_str(" absent"),
                        }
                    }
                    text.push_str("] more=");
                    child!(row.more);
                    let _ = write!(text, " closed={} fixed={}", row.closed, row.fixed);
                    if row.name != NONE {
                        text.push_str(" name=");
                        self.write_path(&mut text, row.name, false);
                        text.push('<');
                        for k in 0..row.name_args.len {
                            if k > 0 {
                                text.push_str(", ");
                            }
                            child!(self.g.ns_at(row.name_args, k));
                        }
                        text.push('>');
                    }
                }
                Desc::Poly { body, vars } => {
                    text.push_str("poly[");
                    for i in 0..vars.len {
                        if i > 0 {
                            text.push_str(", ");
                        }
                        child!(self.g.slot(vars, i));
                    }
                    text.push_str("] ");
                    child!(body);
                }
                Desc::Package { row, args } => {
                    let package = self.g.v.p.packages[row as usize];
                    text.push_str("package(");
                    self.write_path(&mut text, package.path, false);
                    let count = package.longidents.len.min(args.len);
                    for i in 0..count {
                        text.push_str(" with ");
                        let lid = self.g.v.p.indices[(package.longidents.start + i) as usize];
                        self.g.v.write_longident(&mut text, lid, LongidentStyle::Structural);
                        text.push_str(" = ");
                        child!(self.g.slot(args, i));
                    }
                    text.push(')');
                }
            }
            text.push(')');
            flush!();
            debug_assert_eq!(start, text.len());
            work[first..].reverse();
        }
        self.work = work;
        self.text = text;
    }


}

/// `{:?}` of `decl::RecStatus`.
fn rec_status(status: ItemStatus) -> &'static str {
    match status {
        ItemStatus::Recursive(RecStatus::First) => "TrecFirst",
        ItemStatus::Recursive(RecStatus::Next) => "TrecNext",
        _ => "TrecNot",
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn work_item_sizes() {
        assert_eq!(std::mem::size_of::<super::PrintTask>(), 12);
        assert_eq!(std::mem::size_of::<super::Step>(), 8);
        assert_eq!(std::mem::size_of::<super::NodeNumber>(), 8);
        assert_eq!(std::mem::size_of::<super::Own>(), 16);
        assert_eq!(std::mem::size_of::<super::PathStep>(), 8);
    }
}
