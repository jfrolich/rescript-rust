//! Canonical text of a compilation unit's exported signature.
//!
//! Two type checkers (or two versions of one) export the same interface when
//! this text is the same. It does not depend on node identity (which handle
//! a type has), on identifier stamps, on levels other than
//! "generic or not", or on whether the unit's own items are named by local
//! identifier (`t`) or through the unit (`Unit.t`): printing a signature,
//! storing it, reading it back into another [`TypeContext`] and printing it
//! again gives the same text.
//!
//! The text has two parts:
//!
//! 1. The signature as the type printer prints it for a user (`printtyp`,
//!    through the outcome tree, which names variables by traversal).
//! 2. Per item, what the printer leaves out and a dependent can read: every
//!    type by structure (paths with the `Pdot` positions of other units'
//!    items, row and object details, which nodes are shared), runtime
//!    representations (record
//!    and variant layouts, `@unboxed`, runtime names and tags), variance,
//!    primitive descriptions, attributes, and the unit's deprecation.
//!
//! Left out on purpose: locations (the diagnostics that quote them are
//! compared separately), `val_path`/`type_path`/`md_path` (they repeat the
//! item's position in the signature), `type_newtype_level` (levels), and the
//! allocation identity of a recognized shape.

use std::fmt::Write as _;

use super::btype;
use super::context::TypeContext;
use super::decl::{
    Attribute, AttributePayload, ConstructorArguments, ExtensionConstructor, LabelDeclaration,
    ModuleType, RecordRepresentation, SignatureItem, TypeDeclaration, TypeInlinedType, TypeKind,
    ValueDescription, ValueKind,
};
use super::path::{NOPOS, Path, PathView};
use super::printtyp::{Printtyp, print_out_module_type};
use super::type_expr::{GENERIC_LEVEL, RowField, TypeDesc, TypeExprRef};
use super::variant_runtime::{
    Block, BlockType, ConstructorCase, Instance, Layout, TaggedBlock, ValueShape,
};
use crate::parse_arena::ParseArena;
use crate::parser::longident::Longident;

/// The canonical text of the signature `sig` of the unit named `unit` (see
/// the module documentation). `deprecated` is the unit's own deprecation.
/// `arena` resolves the names of package-type constraints written in the
/// unit being compiled; a signature read back from a store needs none.
pub fn canonical_signature(
    ctx: &TypeContext,
    unit: &str,
    sig: &[SignatureItem],
    deprecated: Option<&str>,
    arena: Option<&ParseArena>,
) -> String {
    let unit_path = Path::pident(crate::ident::Ident::create_persistent(unit));
    let mut out = String::new();
    let _ = writeln!(out, "unit {unit}");
    if let Some(reason) = deprecated {
        let _ = writeln!(out, "deprecated {reason:?}");
    }
    out.push_str("== printed\n");
    let tree = Printtyp::new(ctx).tree_of_modtype_in_unit(
        &ModuleType::MtySignature(std::sync::Arc::new(sig.to_vec())),
        &unit_path,
    );
    out.push_str(&print_out_module_type(&tree));
    out.push_str("\n== items\n");
    let mut printer = Canonical {
        ctx,
        arena,
        unit_path,
        own_items: Vec::new(),
        module_prefix: String::new(),
        out,
        indent: 0,
        numbers: NodeNumbers::default(),
    };
    printer.signature(sig, true);
    printer.out
}

/// Where a path starts.
enum PathRoot {
    /// The path is the unit itself.
    Unit,
    /// One of the unit's own items.
    Own,
    /// Another unit, a predefined type, a functor parameter, or an item
    /// local to a module type.
    Other,
}

/// A payload kind without the allocation identity of a class's blocks,
/// which is not part of what the kind says.
fn block_type_text(block_type: &BlockType) -> String {
    match block_type {
        BlockType::Instance(Instance::Array(_)) => "Instance(Array)".to_string(),
        BlockType::Instance(Instance::Class {
            name, ancestors, ..
        }) => format!("Instance({name} extends {ancestors:?})"),
        BlockType::Number
        | BlockType::String
        | BlockType::Bigint
        | BlockType::Boolean
        | BlockType::Symbol
        | BlockType::Function
        | BlockType::Object
        | BlockType::Unknown => format!("{block_type:?}"),
    }
}

/// A variant's runtime representation. Its matching facts are derived from
/// the constructors, so only the constructors are printed.
fn layout_text(layout: &Layout) -> String {
    let mut text = format!(
        "unboxed={} tag_name={:?} [",
        layout.unboxed, layout.matching_facts.tag_name
    );
    for (index, constructor) in layout.constructors.iter().enumerate() {
        if index > 0 {
            text.push_str(", ");
        }
        match constructor {
            ConstructorCase::Constant(tag) => {
                let _ = write!(text, "{}=Constant({:?})", tag.name.as_str(), tag.literal);
            }
            ConstructorCase::Block(Block::Tagged(TaggedBlock { tag, tag_name })) => {
                let _ = write!(
                    text,
                    "{}=Tagged({:?}, tag_name={tag_name:?})",
                    tag.name.as_str(),
                    tag.literal,
                );
            }
            ConstructorCase::Block(Block::Untagged { tag, block_type }) => {
                let _ = write!(
                    text,
                    "{}=Untagged({:?}, {})",
                    tag.name.as_str(),
                    tag.literal,
                    block_type_text(block_type),
                );
            }
        }
    }
    text.push(']');
    text
}

/// Eight bytes per populated dense-table slot; epochs avoid a clearing walk.
#[derive(Clone, Copy, Default)]
struct NodeNumber {
    epoch: u32,
    number: u32,
}

#[derive(Default)]
struct NodeNumbers {
    tiers: [Vec<NodeNumber>; 3],
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
    fn number(&mut self, ty: TypeExprRef, variable: bool) -> (u32, bool) {
        let (tier, index) = if ty.is_shared() {
            (2, ty.shared_index() as usize)
        } else if ty.is_store() {
            (1, ty.store_index())
        } else {
            (0, ty.index())
        };
        let table = &mut self.tiers[tier];
        if index >= table.len() {
            table.resize((index + 1).next_power_of_two(), NodeNumber::default());
        }
        let slot = &mut table[index];
        // Epoch zero is the empty sentinel, including before the first clear.
        if slot.epoch != 0 && slot.epoch == self.epoch {
            return (slot.number, false);
        }
        let next = if variable { &mut self.variables } else { &mut self.structures };
        *slot = NodeNumber { epoch: self.epoch, number: *next };
        *next = next.checked_add(1).expect("too many canonical nodes");
        (slot.number, true)
    }
}

/// Twelve-byte work item; text is in one shared byte pool, never owned per node.
#[derive(Clone, Copy)]
enum PrintTask {
    Type(TypeExprRef),
    Text { start: u32, end: u32 },
}

struct Canonical<'a> {
    ctx: &'a TypeContext,
    arena: Option<&'a ParseArena>,
    /// `Pident unit`: a path through it names one of the unit's own items.
    unit_path: Path,
    /// The types, modules and module types of the unit's own structure that
    /// are in scope, innermost last, with their names from the unit's top
    /// (`Inner.Deep.t`). A signature as type-checked names them by local
    /// identifier; a stored one names them through the unit.
    own_items: Vec<(crate::ident::Ident, String)>,
    /// The name from the unit's top of the module whose signature is being
    /// printed, with a trailing dot; empty at the top.
    module_prefix: String,
    out: String,
    indent: usize,
    numbers: NodeNumbers,

}

impl Canonical<'_> {
    fn line(&mut self, text: &str) {
        for _ in 0..self.indent {
            self.out.push_str("  ");
        }
        self.out.push_str(text);
        self.out.push('\n');
    }

    /// The signature of the unit or of one of its modules (`components` is
    /// true), whose items a stored signature names from the unit's top; or
    /// one inside a module type or a functor, whose items stay local in
    /// both forms (OCaml's `prefix_idents` stops there too).
    fn signature(&mut self, sig: &[SignatureItem], components: bool) {
        let in_scope = self.own_items.len();
        if components {
            for item in sig {
                match item {
                    SignatureItem::SigType(id, _, _)
                    | SignatureItem::SigModule(id, _, _)
                    | SignatureItem::SigModtype(id, _) => {
                        let name = format!("{}{}", self.module_prefix, id.name());
                        self.own_items.push((*id, name));
                    }
                    SignatureItem::SigValue(..)
                    | SignatureItem::SigTypext(..)
                    | SignatureItem::SigClass
                    | SignatureItem::SigClassType => {}
                }
            }
        }
        for item in sig {
            // Sharing is recorded within an item, never across items.
            self.numbers.clear();
            match item {
                SignatureItem::SigValue(id, decl) => self.value(id.name(), decl),
                SignatureItem::SigType(id, decl, rec) => {
                    self.line(&format!("type {} {rec:?}", id.name()));
                    self.indent += 1;
                    self.type_declaration(decl);
                    self.indent -= 1;
                }
                SignatureItem::SigTypext(id, ext, status) => {
                    self.line(&format!("typext {} {status:?}", id.name()));
                    self.indent += 1;
                    self.extension_constructor(ext);
                    self.indent -= 1;
                }
                SignatureItem::SigModule(id, decl, rec) => {
                    self.line(&format!("module {} {rec:?}", id.name()));
                    self.indent += 1;
                    self.attributes(&decl.md_attributes);
                    let prefix = self.module_prefix.clone();
                    if components {
                        let _ = write!(self.module_prefix, "{}.", id.name());
                    }
                    self.module_type(&decl.md_type, components);
                    self.module_prefix = prefix;
                    self.indent -= 1;
                }
                SignatureItem::SigModtype(id, decl) => {
                    self.line(&format!("modtype {}", id.name()));
                    self.indent += 1;
                    self.attributes(&decl.mtd_attributes);
                    match &decl.mtd_type {
                        Some(mty) => self.module_type(mty, false),
                        None => self.line("abstract"),
                    }
                    self.indent -= 1;
                }
                SignatureItem::SigClass => self.line("class"),
                SignatureItem::SigClassType => self.line("classtype"),
            }
        }
        self.own_items.truncate(in_scope);
    }

    /// `components`: whether a signature here is that of one of the unit's
    /// modules (see [`Self::signature`]).
    fn module_type(&mut self, mty: &ModuleType, components: bool) {
        match mty {
            ModuleType::MtyIdent(path) => {
                let path = self.path(path);
                self.line(&format!("ident {path}"));
            }
            ModuleType::MtyAlias(presence, path) => {
                let path = self.path(path);
                self.line(&format!("alias {presence:?} {path}"));
            }
            ModuleType::MtySignature(sig) => {
                self.line("sig");
                self.indent += 1;
                // The enclosing item's variables are not visible inside.
                let numbers = std::mem::take(&mut self.numbers);
                self.signature(sig, components);
                self.numbers = numbers;
                self.indent -= 1;
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                self.line(&format!("functor {}", param.name()));
                self.indent += 1;
                match param_type {
                    Some(mty) => self.module_type(mty, false),
                    None => self.line("generative"),
                }
                self.line("result");
                self.module_type(result, false);
                self.indent -= 1;
            }
        }
    }

    fn value(&mut self, name: &str, decl: &ValueDescription) {
        let ty = self.type_text(decl.val_type);
        self.line(&format!("value {name}: {ty}"));
        self.indent += 1;
        match &decl.val_kind {
            ValueKind::ValReg => {}
            ValueKind::ValPrim(prim) => self.line(&format!(
                "prim {:?} arity={} native_float={} from_constructor={} {:?}",
                prim.prim_name,
                prim.prim_arity,
                prim.prim_native_float,
                prim.prim_from_constructor,
                prim.prim_kind,
            )),
        }
        self.attributes(&decl.val_attributes);
        self.indent -= 1;
    }

    fn type_declaration(&mut self, decl: &TypeDeclaration) {
        let params = self.type_list_text(&decl.type_params);
        self.line(&format!(
            "params [{params}] arity={} {:?} immediate={} {:?}",
            decl.type_arity, decl.type_private, decl.type_immediate, decl.type_representation,
        ));
        self.line(&format!("variance {:?}", decl.type_variance));
        match &decl.type_shape {
            ValueShape::Unstated => {}
            ValueShape::NeverUndefined => self.line("shape never-undefined"),
            ValueShape::RecognizedAs(shape) => {
                self.line(&format!("shape {}", block_type_text(&shape.block_type)));
            }
        }
        if let Some(manifest) = decl.type_manifest {
            let manifest = self.type_text(manifest);
            self.line(&format!("manifest {manifest}"));
        }
        self.attributes(&decl.type_attributes);
        match &decl.type_kind {
            TypeKind::TypeAbstract => self.line("abstract"),
            TypeKind::TypeOpen => self.line("open"),
            TypeKind::TypeRecord(labels, repr) => {
                let repr = self.record_representation(repr);
                self.line(&format!("record {repr}"));
                self.labels(labels);
            }
            TypeKind::TypeVariant(constructors, layout) => {
                self.line(&format!(
                    "variant {}",
                    layout_text(&self.ctx.variant_layout(*layout))
                ));
                self.indent += 1;
                for constructor in constructors.iter() {
                    let res = match constructor.cd_res {
                        Some(res) => format!(": {}", self.type_text(res)),
                        None => String::new(),
                    };
                    self.line(&format!(
                        "constructor {} tag={:?}{res}",
                        constructor.cd_id.name(),
                        constructor.cd_runtime_tag,
                    ));
                    self.indent += 1;
                    self.attributes(&constructor.cd_attributes);
                    self.constructor_arguments(&constructor.cd_args);
                    self.indent -= 1;
                }
                self.indent -= 1;
            }
        }
        for inlined in &decl.type_inlined_types {
            match inlined {
                TypeInlinedType::Record { type_name, labels } => {
                    self.line(&format!("inlined record {type_name}"));
                    self.labels(labels);
                }
            }
        }
    }

    fn record_representation(&self, repr: &RecordRepresentation) -> String {
        match repr {
            RecordRepresentation::RecordInlined {
                name,
                representation,
            } => format!(
                "RecordInlined {name} position={} {}",
                representation.position,
                layout_text(&self.ctx.variant_layout(representation.variant)),
            ),
            RecordRepresentation::RecordRegular
            | RecordRepresentation::RecordArray
            | RecordRepresentation::RecordUnboxed(_)
            | RecordRepresentation::RecordExtension => format!("{repr:?}"),
        }
    }

    fn labels(&mut self, labels: &[LabelDeclaration]) {
        self.indent += 1;
        for label in labels {
            let ty = self.type_text(label.ld_type);
            self.line(&format!(
                "label {} runtime={:?} {:?} optional={}: {ty}",
                label.ld_id.name(),
                label.ld_runtime_name,
                label.ld_mutable,
                label.ld_optional,
            ));
            self.indent += 1;
            self.attributes(&label.ld_attributes);
            self.indent -= 1;
        }
        self.indent -= 1;
    }

    fn constructor_arguments(&mut self, args: &ConstructorArguments) {
        match args {
            ConstructorArguments::CstrTuple(types) => {
                if !types.is_empty() {
                    let types = self.type_list_text(types);
                    self.line(&format!("args ({types})"));
                }
            }
            ConstructorArguments::CstrRecord(labels) => {
                self.line("args record");
                self.labels(labels);
            }
        }
    }

    fn extension_constructor(&mut self, ext: &ExtensionConstructor) {
        let path = self.path(&ext.ext_type_path);
        let params = self.type_list_text(&ext.ext_type_params);
        let ret = match ext.ext_ret_type {
            Some(ret) => format!(": {}", self.type_text(ret)),
            None => String::new(),
        };
        self.line(&format!(
            "of {path} params [{params}] {:?} exception={}{ret}",
            ext.ext_private, ext.ext_is_exception,
        ));
        self.attributes(&ext.ext_attributes);
        self.constructor_arguments(&ext.ext_args);
    }

    fn attributes(&mut self, attributes: &[Attribute]) {
        for attribute in attributes {
            let payload = match &attribute.attr_payload {
                // The location a malformed payload is reported at is an
                // identity-dependent handle; that it is malformed is not.
                AttributePayload::Deprecated {
                    reason,
                    can_be_automigrated,
                    migrate,
                    migrate_in_pipe_chain,
                } => format!(
                    "Deprecated reason={:?} automigrate={can_be_automigrated} migrate={migrate:?} \
                     migrate_in_pipe_chain={migrate_in_pipe_chain:?}",
                    reason.as_ref().map_err(|_| "invalid"),
                ),
                AttributePayload::SemanticString(payload) => format!(
                    "SemanticString {:?} braces={} template={}",
                    payload.semantic.as_ref().map_err(|_| "invalid"),
                    payload.braces,
                    payload.template,
                ),
                AttributePayload::Empty
                | AttributePayload::Str(_)
                | AttributePayload::Int(_)
                | AttributePayload::IntLiteral(_)
                | AttributePayload::Float(_)
                | AttributePayload::BigInt(_)
                | AttributePayload::Bool(_)
                | AttributePayload::Ident(_)
                | AttributePayload::Structure(_)
                | AttributePayload::StrTuple(_) => format!("{:?}", attribute.attr_payload),
            };
            self.line(&format!("@{} {payload}", attribute.attr_name.txt));
        }
    }

    /// A path by names. One of the unit's own items prints as its name from
    /// the unit's top, whether the path is a local identifier or goes
    /// through the unit, so `t`, `Inner.t` and `Unit.Inner.t` are one text
    /// where they are one item. Any other path keeps the `Pdot` positions
    /// the type printer omits.
    fn path(&self, path: &Path) -> String {
        let mut text = String::new();
        self.write_path(&mut text, path);
        text
    }

    fn write_path(&self, out: &mut String, path: &Path) {
        match self.path_root(path) {
            PathRoot::Unit => {}
            PathRoot::Own => self.write_own_path(out, path),
            PathRoot::Other => self.write_other_path(out, path),
        }
    }

    fn path_root(&self, path: &Path) -> PathRoot {
        if path.same(&self.unit_path) {
            return PathRoot::Unit;
        }
        match path.view() {
            PathView::Pident(id) => {
                if self.own_items.iter().any(|(own, _)| own == id) {
                    PathRoot::Own
                } else {
                    PathRoot::Other
                }
            }
            PathView::Pdot(parent, _, _) => match self.path_root(parent) {
                PathRoot::Unit | PathRoot::Own => PathRoot::Own,
                PathRoot::Other => PathRoot::Other,
            },
            PathView::Papply(..) => PathRoot::Other,
        }
    }

    /// A path rooted in the unit, without the unit and without positions:
    /// the local form of such a path has no `Pdot` for the components the
    /// stored form adds, so their positions are not part of the text.
    fn write_own_path(&self, out: &mut String, path: &Path) {
        match path.view() {
            PathView::Pident(id) => match self.own_items.iter().rev().find(|(own, _)| own == id) {
                Some((_, name)) => out.push_str(name),
                None => out.push_str(id.name()),
            },
            PathView::Pdot(parent, name, _) => {
                if !parent.same(&self.unit_path) {
                    self.write_own_path(out, parent);
                    out.push('.');
                }
                out.push_str(name.as_str());
            }
            PathView::Papply(..) => self.write_other_path(out, path),
        }
    }

    fn write_other_path(&self, out: &mut String, path: &Path) {
        match path.view() {
            PathView::Pident(id) => out.push_str(id.name()),
            PathView::Pdot(parent, name, pos) => {
                self.write_other_path(out, parent);
                out.push('.');
                out.push_str(name.as_str());
                if *pos != NOPOS {
                    let _ = write!(out, "@{pos}");
                }
            }
            PathView::Papply(functor, arg) => {
                self.write_path(out, functor);
                out.push('(');
                self.write_path(out, arg);
                out.push(')');
            }
        }
    }

    fn type_text(&mut self, ty: TypeExprRef) -> String {
        let mut text = String::new();
        self.write_type(&mut text, ty);
        text
    }

    fn type_list_text(&mut self, types: &[TypeExprRef]) -> String {
        let mut text = String::new();
        self.write_types(&mut text, types.iter().copied());
        text
    }

    fn write_types(&mut self, out: &mut String, types: impl IntoIterator<Item = TypeExprRef>) {
        for (index, ty) in types.into_iter().enumerate() {
            if index > 0 {
                out.push_str(", ");
            }
            self.write_type(out, ty);
        }
    }

    /// Amortized O(1), plus output bytes: define a structure on its first visit,
    /// then reference its traversal number. Dense tables are keyed by storage tier.
    /// OCaml ctype.ml's instance copies each generic node once; observing sharing
    /// here distinguishes fixture 07b's repeated node from two equal nodes.
    fn write_shared(&mut self, out: &mut String, ty: TypeExprRef) -> bool {
        let (number, fresh) = self.numbers.number(ty, false);
        if fresh {
            let _ = write!(out, "&{number}(");
        } else {
            let _ = write!(out, "@{number}");
        }
        fresh
    }

    /// O(nodes + edges + output bytes), excluding existing path/row normalization.
    /// One explicit task pool and text pool replace recursion; shared nodes are
    /// expanded once per item. Returns the number of dispatched tasks for tests.
    fn write_type(&mut self, output: &mut String, root: TypeExprRef) -> u64 {
        let mut work = vec![PrintTask::Type(root)];
        let mut text = String::new();
        let mut steps = 0;
        while let Some(task) = work.pop() {
            steps += 1;
            let ty = match task {
                PrintTask::Text { start, end } => {
                    output.push_str(&text[start as usize..end as usize]);
                    continue;
                }
                PrintTask::Type(ty) => self.ctx.repr(ty),
            };
            let ctx = self.ctx;
            let desc = ctx.get_desc(ty).into_desc();
            if let TypeDesc::Tvar(name) | TypeDesc::Tunivar(name) = desc {
                let (index, _) = self.numbers.number(ty, true);
                output.push(if matches!(desc, TypeDesc::Tvar(_)) { '\'' } else { '!' });
                if ctx.get_level(ty) != GENERIC_LEVEL { output.push('_'); }
                let _ = write!(output, "{index}");
                if let Some(name) = name { let _ = write!(output, ":{}", name.as_str()); }
                continue;
            }
            if !self.write_shared(output, ty) { continue; }
            let first = work.len();
            let out = &mut text;
            let mut start = out.len();
            macro_rules! flush {
                () => {{
                    let end = out.len();
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
                ($ty:expr) => {{ flush!(); work.push(PrintTask::Type($ty)); }};
            }
            macro_rules! children {
                ($types:expr) => {{
                    for (index, ty) in $types.into_iter().enumerate() {
                        if index > 0 { out.push_str(", "); }
                        child!(ty);
                    }
                }};
            }
        match desc {
            TypeDesc::Tvar(_)
            | TypeDesc::Tunivar(_)
            | TypeDesc::Tlink(_)
            | TypeDesc::Tsubst(_) => out.push_str("<link>"),
            TypeDesc::Tnil => out.push_str("nil"),
            TypeDesc::Tarrow { args, ret } => {
                out.push('(');
                for (index, arg) in ctx.type_args(args).iter().enumerate() {
                    if index > 0 {
                        out.push_str(", ");
                    }
                    let label = arg.label();
                    if let Some(name) = label.label_name() {
                        out.push(if label.is_optional() { '?' } else { '~' });
                        out.push_str(name);
                        out.push(':');
                    }
                    child!(arg.typ);
                }
                out.push_str(") => ");
                child!(ret);
            }
            TypeDesc::Ttuple(types) => {
                out.push_str("tuple(");
                children!(ctx.type_list(types).iter());
                out.push(')');
            }
            TypeDesc::Tconstr { path, args, .. } => {
                self.write_path(out, &path);
                if !args.is_empty() {
                    out.push('<');
                    children!(ctx.type_list(args).iter());
                    out.push('>');
                }
            }
            TypeDesc::Tobject { fields } => {
                out.push_str("object{");
                child!(fields);
                out.push('}');
            }
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                let _ = write!(
                    out,
                    "{}[{:?}]: ",
                    name.as_str(),
                    ctx.mutability_repr(mutability)
                );
                child!(typ);
                out.push_str("; ");
                child!(rest);
            }
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(row);
                let row = btype::row_repr(ctx, &row);
                out.push_str("variant[");
                for (index, (label, field)) in row.row_fields.iter().enumerate() {
                    if index > 0 {
                        out.push_str(" | ");
                    }
                    let _ = write!(out, "#{label}");
                    match btype::row_field_repr(ctx, field) {
                        RowField::Rpresent(None) => {}
                        RowField::Rpresent(Some(ty)) => {
                            out.push('(');
                            child!(ty);
                            out.push(')');
                        }
                        RowField::Reither {
                            constant,
                            types,
                            matched,
                            ..
                        } => {
                            let _ = write!(out, " either constant={constant} matched={matched} (");
                            children!(types);
                            out.push(')');
                        }
                        RowField::Rabsent => out.push_str(" absent"),
                    }
                }
                out.push_str("] more=");
                child!(row.row_more);
                let _ = write!(out, " closed={} fixed={}", row.row_closed, row.row_fixed);
                if let Some((path, args)) = &row.row_name {
                    out.push_str(" name=");
                    self.write_path(out, path);
                    out.push('<');
                    children!(args.iter().copied());
                    out.push('>');
                }
            }
            TypeDesc::Tpoly { body, vars } => {
                out.push_str("poly[");
                children!(ctx.type_list(vars).iter());
                out.push_str("] ");
                child!(body);
            }
            TypeDesc::Tpackage { path, lids, args } => {
                out.push_str("package(");
                self.write_path(out, &path);
                let lids = ctx.package_lids(lids);
                for (lid, arg) in lids.iter().zip(ctx.type_list(args).iter()) {
                    out.push_str(" with ");
                    self.write_longident(out, lid);
                    out.push_str(" = ");
                    child!(arg);
                }
                out.push(')');
            }
        }

            out.push(')');
            flush!();
            debug_assert_eq!(start, out.len());
            work[first..].reverse();
        }
        steps
    }

    fn write_longident(&self, out: &mut String, lid: &Longident) {
        match lid {
            Longident::Lident(name) => self.write_longident_component(out, *name),
            Longident::Ldot(prefix, name) => {
                self.write_longident(out, prefix);
                out.push('.');
                self.write_longident_component(out, *name);
            }
            Longident::Lapply(functor, arg) => {
                self.write_longident(out, functor);
                out.push('(');
                self.write_longident(out, arg);
                out.push(')');
            }
        }
    }

    fn write_longident_component(&self, out: &mut String, name: crate::intern::StrIdx) {
        match (self.ctx.resolve_cmi_longident_component(name), self.arena) {
            (Some(name), _) => out.push_str(&name),
            (None, Some(arena)) => out.push_str(arena.get_string(name)),
            (None, None) => out.push_str("<unresolved>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::canonical_signature;
    use crate::cmi::persistent_env::ModuleRegistry;
    use crate::cmi::portable_types::internalize_pers_struct;
    use crate::context::IdGenerator;
    use crate::driver::{CompilerOptions, DumpKind, compile_source_in_process};
    use crate::types::TypeContext;

    /// A signature with every kind of item, shared and recursive types,
    /// rows, objects, runtime representations and attributes.
    const SOURCE: &str = r#"
type rec tree<'a> = Leaf | Node({left: tree<'a>, value: 'a, right: tree<'a>})
@unboxed type wrapped = Wrapped(string)
type color = | @as("r") Red | @as(2) Green | Blue(int, string)
type point = {x: int, mutable y: int, @as("zed") z?: float}
type shape = [#circle(float) | #square]
type rec list2<'a> = [#nil | #cons('a, list2<'a>)]
type obj = {"name": string, "age": int}
type abstract
@instanceOf("Date") type date
@unboxed type dated = Stamp(date) | Text(string)
type alias<'a> = array<option<'a>>
exception Failed(string, int)
external length: string => int = "%string_length"
@deprecated("use other") let old = 1
let id = x => x
let pair = (x, y) => (x, y, x)
let apply = (~f, ~default=?, x) => (f(x), default)
let poly = (x: [> #a | #b(int)]) => x
let loop = (_: [#more('self)] as 'self) => 1
let point = {x: 1, y: 2}
let tree = Node({left: Leaf, value: 1, right: Leaf})
module Inner = {
  type t = int
  type u = point
  let make = (n: t): u => {x: n, y: n}
  module Deep = {
    type v = (t, u)
    let get = ((a, _): v) => a
  }
}
module Alias = Inner
module type Showable = {
  type t
  let show: t => string
}
module MakeShow = (S: Showable) => {
  let twice = (x: S.t) => S.show(x) ++ S.show(x)
}
let inner = Inner.make(1)
let deep: Inner.Deep.v = (1, inner)
"#;

    fn compile(source: &str, unit: &str) -> crate::driver::InProcessCompileResult {
        let options = CompilerOptions {
            nopervasives: true,
            dumps: vec![DumpKind::Sig],
            ..Default::default()
        };
        compile_source_in_process(
            source,
            &format!("{unit}.res"),
            unit,
            &options,
            &ModuleRegistry::new(),
            false,
            None,
        )
        .expect("compiles")
    }

    fn type_text(ctx: &TypeContext, ty: crate::types::TypeExprRef) -> (String, u64) {
        let mut printer = super::Canonical {
            ctx, arena: None,
            unit_path: crate::types::Path::pident(crate::ident::Ident::create_persistent("Test")),
            own_items: Vec::new(), module_prefix: String::new(), out: String::new(),
            indent: 0, numbers: super::NodeNumbers::default(),
        };
        printer.numbers.clear();
        let mut text = String::new();
        let steps = printer.write_type(&mut text, ty);
        (text, steps)
    }

    #[test]
    fn fixture_07b_shared_int_differs_from_two_occurrences() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let path = crate::types::Path::pident(crate::ident::Ident::create_persistent("int"));
        let one = ctx.new_constr(path, vec![]);
        let other = ctx.new_constr(path, vec![]);
        let dup = ctx.new_tuple(vec![one, one]);
        let two = ctx.new_tuple(vec![one, other]);
        assert_ne!(type_text(&ctx, dup).0, type_text(&ctx, two).0);
        // A shift in allocation identities changes neither the numbering nor sharing.
        let shifted = ctx.new_constr(path, vec![]);
        let shifted_dup = ctx.new_tuple(vec![shifted, shifted]);
        assert_eq!(type_text(&ctx, dup).0, type_text(&ctx, shifted_dup).0);
    }

    #[test]
    fn ten_thousand_deep_types_use_a_bounded_explicit_stack() {
        std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
            let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
            let mut ty = ctx.new_var(None);
            for _ in 0..10000 { ty = ctx.new_tuple(vec![ty]); }
            let (text, steps) = type_text(&ctx, ty);
            assert_eq!(text.matches("tuple(").count(), 10000);
            assert!(steps <= 3 * 10000 + 1, "{steps}");
            let wide = ctx.new_tuple(vec![ty; 10000]);
            let (_, steps) = type_text(&ctx, wide);
            assert!(steps <= 5 * 10000 + 3, "{steps}");
        }).unwrap().join().unwrap();
    }

    #[test]
    fn canonical_work_and_slot_sizes() {
        assert_eq!(std::mem::size_of::<super::NodeNumber>(), 8);
        assert_eq!(std::mem::size_of::<super::PrintTask>(), 12);
    }

    const PRELUDE: &str = "type option<'a> = None | Some('a)\n\
        external \\\"++\": (string, string) => string = \"%string_concat\"\n";

    fn sig_dump(result: &crate::driver::InProcessCompileResult) -> String {
        let (kind, text) = result.dumps.first().expect("the sig dump");
        assert_eq!(*kind, DumpKind::Sig);
        text.clone()
    }

    /// The invariant of the canonical form: the text of the signature as
    /// type-checked equals the text of the same signature stored in
    /// portable form and read back into another context, where every handle
    /// differs and the unit's own types are named through the unit.
    #[test]
    fn printing_a_stored_signature_read_back_gives_the_same_text() {
        let mut result = compile(&format!("{PRELUDE}{SOURCE}"), "Sample");
        let printed = sig_dump(&result);
        let portable = result.pers_struct.take().expect("the published signature");
        let deprecated = portable.ps_deprecated.clone();

        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        // Shift every handle of the second context.
        for _ in 0..1000 {
            ctx.new_var(None);
        }
        let stored = internalize_pers_struct(portable, &ctx);
        let reprinted = canonical_signature(
            &ctx,
            "Sample",
            stored.ps_sig.as_ref(),
            deprecated.as_deref(),
            None,
        );
        assert_eq!(printed, reprinted);
    }

    /// Stamps and handles move when unrelated code is added before the
    /// items; the text does not.
    #[test]
    fn the_text_is_independent_of_stamps_and_handles() {
        let plain = sig_dump(&compile(&format!("{PRELUDE}{SOURCE}"), "Sample"));
        // The extra bindings are private to the block, so they take stamps
        // and type nodes without adding an item.
        let shifted = sig_dump(&compile(
            &format!(
                "{PRELUDE}let shift = {{\n  let a = (x, y) => (y, x)\n  let b = a(1, \"s\")\n  b\n}}\n{SOURCE}"
            ),
            "Sample",
        ));
        let without_shift = shifted
            .lines()
            .filter(|line| !line.contains("shift"))
            .collect::<Vec<_>>();
        let plain_lines = plain.lines().collect::<Vec<_>>();
        assert_eq!(plain_lines, without_shift, "{shifted}");
    }

    /// What the type printer omits is in the text: runtime names and tags,
    /// representations, variance, primitives, attributes, sharing of
    /// variables, and a different interface gives a different text.
    #[test]
    fn the_text_has_what_dependents_read() {
        let text = sig_dump(&compile(&format!("{PRELUDE}{SOURCE}"), "Sample"));
        for expected in [
            "unit Sample\n",
            "== printed\n",
            "== items\n",
            "constructor Red tag=Some(String(\"r\"))",
            "constructor Green tag=Some(Int(2))",
            "Unboxed",
            "variant unboxed=true tag_name=None [Wrapped=Untagged(String(\"Wrapped\"), String)]",
            "Stamp=Untagged(String(\"Stamp\"), Instance(Date extends []))",
            "prim \"%string_length\" arity=1",
            "@deprecated Str(\"use other\")",
            // One variable twice, another once.
            // A type that contains itself refers to itself by depth.
            "alias MtaAbsent Inner",
            // One of the unit's own nested items, from the unit's top.
        ] {
            assert!(text.contains(expected), "missing {expected:?} in:\n{text}");
        }
        let shapes = text.lines().map(str::trim).filter(|line| {
            line.starts_with("label z ") || line.starts_with("value pair:")
                || line.starts_with("value loop:") || line.starts_with("value get:")
        }).collect::<Vec<_>>().join("\n");
        crate::expect_dump!(shapes, "label z runtime=Some(\"zed\") Immutable optional=true: &2(option<&3(float)>)\nvalue pair: &0(('0, '1) => &1(tuple('0, '1, '0)))\nvalue loop: &0((&1(variant[#more(@1)] more=&2(nil) closed=true fixed=false)) => &3(int))\nvalue get: &0((&1(Inner.Deep.v)) => &2(Inner.t))");
        // No handle, stamp or location leaks through a `Debug` rendering.
        for forbidden in [
            "TypeExprRef",
            "DeclLoc",
            "stamp",
            "LayoutRef",
            "ShapeAllocation",
            "scope",
        ] {
            assert!(!text.contains(forbidden), "{forbidden} in:\n{text}");
        }

        let changed = sig_dump(&compile(
            &format!(
                "{PRELUDE}{}",
                SOURCE.replace("@as(2) Green", "@as(3) Green")
            ),
            "Sample",
        ));
        assert_ne!(text, changed);
    }
}
