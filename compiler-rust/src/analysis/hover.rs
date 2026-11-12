//! A port of analysis/src/hover.ml (and markdown.ml).
//!
//! Types are printed in the context of the module they come from, so the
//! types hover gathers travel with their module ([`ModuleId`]).

use super::references::{self, Defined};
use super::resolve_path::{self, Session};
use super::session::{Loaded, ProjectSession};
use super::shared::{self, decl_to_string, type_to_string};
use super::shared_types::*;
use super::uri::UriStyle;
use crate::types::decl::{self, RecStatus, TypeDeclaration};
use crate::types::typedtree::Constant;
use crate::types::{Path, TypeDesc, TypeExprRef};
use std::collections::BTreeSet;

/// `Markdown.spacing`.
const SPACING: &str = "\n```\n \n```\n";
/// `Markdown.divider`.
const DIVIDER: &str = "\n---\n";

/// `Markdown.code_block`.
pub fn code_block(code: &str) -> String {
    format!("```rescript\n{code}\n```")
}

/// `Markdown.go_to_definition_text`: a file link with one-based line and
/// column fragments (`Markdown.make_goto_command`).
fn go_to_definition_text(style: UriStyle, file_uri: &str, pos: Pos) -> String {
    let (line, character) = pos.line_col();
    format!(
        "\nGo to: [Type definition]({}#L{},{})",
        style.to_string(file_uri),
        line + 1,
        character + 1
    )
}

/// What hovering works with: the session and the command's options.
pub struct Hover<'h, 's> {
    /// The modules the hovered file can refer to.
    pub session: &'h ProjectSession<'s>,
    /// How URIs in the hover text are printed.
    pub style: UriStyle,
    /// Whether the client renders command links in Markdown.
    pub supports_markdown_links: bool,
}

/// `extracted_type`.
struct ExtractedType {
    name: String,
    path: Path,
    decl: std::sync::Arc<TypeDeclaration>,
    env: QueryEnv,
    loc: Loc,
}

/// `is_inline_record_definition`: whether `path` names one of the inline
/// records of `decl`'s declaration group.
fn is_inline_record_definition(decl: &TypeDeclaration, path: &Path) -> bool {
    let name = path.last();
    decl.type_inlined_types
        .iter()
        .any(|decl::TypeInlinedType::Record { type_name, .. }| type_name == name)
}

impl Hover<'_, '_> {
    fn type_string(&self, module: ModuleId, t: TypeExprRef) -> String {
        type_to_string(self.session.types(module), t, 60)
    }

    /// `show_module_top_level`; the items' types are `module`'s.
    fn show_module_top_level(
        &self,
        module: ModuleId,
        docstring: &[String],
        is_type: bool,
        name: &str,
        top_level: &[ModuleItem],
    ) -> String {
        let types = self.session.types(module);
        let contents: Vec<String> = top_level
            .iter()
            .map(|item| match &item.kind {
                ModuleItemKind::Type(t, rec_status) => {
                    format!(
                        "  {}",
                        decl_to_string(types, &item.name, &t.decl, *rec_status, false)
                    )
                }
                ModuleItemKind::Module { .. } => format!("  module {}", item.name),
                ModuleItemKind::Value(typ) => {
                    format!("  let {}: {}", item.name, type_to_string(types, *typ, 60))
                }
            })
            .collect();
        let name = shared::cut_after_dash(name);
        let full = code_block(&format!(
            "module {}{{\n{}\n}}",
            if is_type {
                format!("type {name} = ")
            } else {
                format!("{name}: ")
            },
            contents.join("\n")
        ));
        let doc = if docstring.is_empty() {
            String::new()
        } else {
            format!("\n{}{DIVIDER}{SPACING}", docstring.join("\n"))
        };
        doc + &full
    }

    /// `show_module`. `owner` is the module `declared`'s types belong to;
    /// OCaml recurses with the original `file` after resolving a module
    /// reference, which only matters when nothing more is declared.
    fn show_module(
        &self,
        docstring: &[String],
        file: &File,
        owner: ModuleId,
        name: &str,
        declared: Option<&Declared<Module>>,
    ) -> Option<String> {
        match declared {
            None => Some(self.show_module_top_level(
                file.module,
                docstring,
                false,
                name,
                &file.structure.items,
            )),
            Some(Declared {
                item: Module::Structure(structure),
                module_path,
                ..
            }) => {
                let is_type = matches!(
                    module_path,
                    ModulePath::ExportedModule { is_type: true, .. }
                );
                Some(self.show_module_top_level(owner, docstring, is_type, name, &structure.items))
            }
            Some(
                declared @ Declared {
                    item: Module::Constraint(_, module_type_item),
                    ..
                },
            ) => {
                // Show the interface.
                let declared = Declared {
                    item: (**module_type_item).clone(),
                    ..declared.clone()
                };
                self.show_module(docstring, file, owner, name, Some(&declared))
            }
            Some(
                declared @ Declared {
                    item: Module::Ident(path),
                    ..
                },
            ) => match references::resolve_module_reference(self.session, file, declared, &[]) {
                None => Some(format!(
                    "Unable to resolve module reference {}",
                    path.name()
                )),
                Some((resolved, declared)) => {
                    self.show_module(docstring, file, resolved.module, name, declared.as_ref())
                }
            },
        }
    }

    /// `find_relevant_types_from_type`. `module` owns `typ`.
    fn find_relevant_types_from_type(&self, file: &File, typ: TypeExprRef) -> Vec<ExtractedType> {
        let types = self.session.types(file.module);
        let env = QueryEnv::from_file(file);
        // The types to search, with the module each belongs to.
        let (env_to_search, types_to_search): (QueryEnv, Vec<(ModuleId, TypeExprRef)>) =
            match shared::dig_constructor(types, typ) {
                Some(path) => match references::dig_constructor(self.session, &env, &path) {
                    None => (env, vec![(file.module, typ)]),
                    Some((env1, declared)) => {
                        let decl_module = env1.file;
                        let label_types = |lds: &[decl::LabelDeclaration]| {
                            lds.iter()
                                .map(|ld| (decl_module, ld.ld_type))
                                .collect::<Vec<_>>()
                        };
                        match &declared.item.decl.type_kind {
                            decl::TypeKind::TypeRecord(lds, _) => {
                                let mut all = vec![(file.module, typ)];
                                all.extend(label_types(lds));
                                (env1, all)
                            }
                            decl::TypeKind::TypeVariant(cds, _) => {
                                let mut all = Vec::new();
                                for cd in cds.iter() {
                                    let from_args: Vec<(ModuleId, TypeExprRef)> = match &cd.cd_args
                                    {
                                        decl::ConstructorArguments::CstrTuple(ts) => {
                                            ts.iter().map(|t| (decl_module, *t)).collect()
                                        }
                                        decl::ConstructorArguments::CstrRecord(lds) => {
                                            label_types(lds)
                                        }
                                    };
                                    all.push((file.module, typ));
                                    if let Some(t) = cd.cd_res {
                                        all.push((decl_module, t));
                                    }
                                    all.extend(from_args);
                                }
                                (env1, all)
                            }
                            _ => (env, vec![(file.module, typ)]),
                        }
                    }
                },
                None => (env, vec![(file.module, typ)]),
            };
        let mut constructors = Vec::new();
        for (module, t) in types_to_search {
            shared::find_type_constructors_in(self.session.types(module), &[t], &mut constructors);
        }
        constructors
            .into_iter()
            .filter_map(|path| {
                let (env, declared) =
                    references::dig_constructor(self.session, &env_to_search, &path)?;
                Some(ExtractedType {
                    name: declared.name.txt.clone(),
                    loc: declared.extent_loc,
                    decl: declared.item.decl.clone(),
                    env,
                    path,
                })
            })
            .collect()
    }

    /// `expand_types`: the expanded definitions, and whether `typ` is an
    /// inline record (OCaml's `` `InlineType ``).
    fn expand_types(&self, file: &File, typ: TypeExprRef) -> (Vec<String>, bool) {
        let all = self.find_relevant_types_from_type(file, typ);
        if let Some(first) = all.first()
            && is_inline_record_definition(&first.decl, &first.path)
        {
            // Inline record types print just with their definition, not the
            // constructor pointing to them.
            let types = self.session.types(first.env.file);
            let name = shared::path_ident_to_string(&first.path);
            return (
                vec![code_block(&decl_to_string(
                    types,
                    &name,
                    &first.decl,
                    RecStatus::TrecNot,
                    true,
                ))],
                true,
            );
        }
        let mut types_seen = BTreeSet::new();
        let expanded = all
            .into_iter()
            // Don't produce duplicate type definitions for recursive types.
            .filter(|t| types_seen.insert(format!("{}.{}", t.env, t.name)))
            .map(|t| {
                let file = self.session.file(t.env.file);
                let link = if self.supports_markdown_links
                    && !is_inline_record_definition(&t.decl, &t.path)
                {
                    go_to_definition_text(self.style, &file.uri, t.loc.start)
                } else {
                    String::new()
                };
                let types = self.session.types(t.env.file);
                let name = shared::path_ident_to_string(&t.path);
                format!(
                    "{DIVIDER}{}{}{link}\n",
                    if self.supports_markdown_links {
                        SPACING
                    } else {
                        ""
                    },
                    code_block(&decl_to_string(
                        types,
                        &name,
                        &t.decl,
                        RecStatus::TrecNot,
                        true
                    ))
                )
            })
            .collect();
        (expanded, false)
    }

    /// `Completion_back_end.show_constructor`; `module` owns its types.
    fn show_constructor(&self, module: ModuleId, constructor: &Constructor) -> String {
        let types = self.session.types(module);
        let args = match &constructor.args {
            ConstructorArgs::Args(args) if args.is_empty() => String::new(),
            ConstructorArgs::InlineRecord(fields) => {
                let fields: Vec<String> = fields
                    .iter()
                    .map(|field| {
                        let t = if field.optional {
                            shared::unwrap_if_option(types, field.typ)
                        } else {
                            field.typ
                        };
                        format!(
                            "{}{}: {}",
                            field.fname.txt,
                            if field.optional { "?" } else { "" },
                            type_to_string(types, t, 60)
                        )
                    })
                    .collect();
                format!("({{{}}})", fields.join(", "))
            }
            ConstructorArgs::Args(args) => {
                let args: Vec<String> = args
                    .iter()
                    .map(|(t, _)| type_to_string(types, *t, 60))
                    .collect();
                format!("({})", args.join(", "))
            }
        };
        let res = match constructor.res {
            None => String::new(),
            Some(t) => format!("\n{}", type_to_string(types, t, 60)),
        };
        format!("{}{args}{res}", constructor.cname.txt)
    }

    /// `hover_with_expanded_types`. `file` owns `typ`.
    fn hover_with_expanded_types(
        &self,
        file: &File,
        docstring: Option<&[String]>,
        constructor: Option<(&Constructor, ModuleId)>,
        typ: TypeExprRef,
    ) -> String {
        let (expanded_types, inline) = self.expand_types(file, typ);
        if inline {
            return expanded_types.join("\n");
        }
        let mut type_string = self.type_string(file.module, typ);
        if let Some((constructor, module)) = constructor {
            type_string = format!(
                "{type_string}\n{}",
                self.show_constructor(module, constructor)
            );
        }
        let type_string = match docstring {
            Some(docstring) if !docstring.is_empty() => {
                format!(
                    "{}{DIVIDER}{}",
                    code_block(&type_string),
                    docstring.join("\n")
                )
            }
            _ => code_block(&type_string),
        };
        let mut parts = vec![type_string];
        parts.extend(expanded_types);
        parts.join("\n")
    }

    /// Show a module found through a stamp of `file`.
    fn show_module_stamp(&self, file: &File, stamp: i32) -> Option<String> {
        let md = file.stamps.find_module(stamp)?;
        let (file, declared) = references::resolve_module_reference(self.session, file, md, &[])?;
        let (name, docstring) = match &declared {
            Some(d) => (d.name.txt.clone(), d.docstring.clone()),
            None => (file.module_name.clone(), file.structure.docstring.clone()),
        };
        self.show_module(&docstring, file, file.module, &name, declared.as_ref())
    }

    /// `new_hover`.
    pub fn new_hover(&self, full: &Loaded, loc_item: &LocItem) -> Option<String> {
        let file = self.session.file(full.file.module);
        match &loc_item.loc_type {
            LocType::TypeDefinition(name, decl, _) => {
                let types = self.session.types(file.module);
                let type_def = code_block(&decl_to_string(
                    types,
                    name,
                    decl,
                    RecStatus::TrecNot,
                    false,
                ));
                match decl.type_manifest {
                    None => Some(type_def),
                    Some(typ) => {
                        let (expanded_types, inline) = self.expand_types(file, typ);
                        if inline {
                            Some(expanded_types.join("\n"))
                        } else {
                            let mut parts = vec![type_def];
                            parts.extend(expanded_types);
                            Some(parts.join("\n"))
                        }
                    }
                }
            }
            LocType::LModule(LocKind::Definition(stamp, _) | LocKind::LocalReference(stamp, _)) => {
                self.show_module_stamp(file, *stamp)
            }
            LocType::LModule(LocKind::GlobalReference(module_name, path, tip)) => {
                let file = self.session.file_for_module(module_name)?;
                let env = QueryEnv::from_file(file);
                let (_, _, stamp) = references::exported_for_tip(self.session, &env, path, tip)?;
                self.show_module_stamp(file, stamp)
            }
            LocType::LModule(LocKind::NotFound) => None,
            LocType::TopLevelModule(name) => {
                let file = self.session.file_for_module(name)?;
                self.show_module(
                    &file.structure.docstring,
                    file,
                    file.module,
                    &file.module_name,
                    None,
                )
            }
            LocType::Typed(_, _, LocKind::Definition(_, Tip::Field(_) | Tip::Constructor(_))) => {
                None
            }
            LocType::Constant(t) => Some(code_block(match t {
                Constant::Int(_) => "int",
                Constant::Char(_) => "char",
                Constant::String(..) => "string",
                Constant::Float(_) => "float",
                Constant::BigInt(..) => "bigint",
            })),
            LocType::Typed(_, t, loc_kind) => {
                let types = self.session.types(file.module);
                // Expand first-class modules to the underlying module type
                // signature.
                let t = shared::dig(types, *t);
                if let TypeDesc::Tpackage { path, .. } = &*types.get_desc(t) {
                    let env = QueryEnv::from_file(file);
                    return match resolve_path::resolve_module_from_compiler_path(
                        self.session,
                        &env,
                        path,
                    ) {
                        Some((env_for_module, Some(declared))) => self.show_module(
                            &declared.docstring,
                            self.session.file(env_for_module.file),
                            env_for_module.file,
                            &path.name(),
                            Some(&declared),
                        ),
                        _ => Some(self.hover_with_expanded_types(file, None, None, t)),
                    };
                }
                Some(
                    match references::defined_for_loc(self.session, file, loc_kind) {
                        None => self.hover_with_expanded_types(file, None, None, t),
                        Some((docstring, Defined::Declared | Defined::Field)) => {
                            self.hover_with_expanded_types(file, Some(&docstring), None, t)
                        }
                        Some((_, Defined::Constructor(constructor, module))) => self
                            .hover_with_expanded_types(
                                file,
                                Some(&constructor.docstring),
                                Some((&constructor, module)),
                                t,
                            ),
                    },
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// tests/analysis_tests/tests/src/expected/Hover.res.txt:129: the link
    /// names the file and the one-based line and column.
    #[test]
    fn links_to_definitions_by_file_fragment() {
        let pos = Pos {
            line: 111,
            bol: 100,
            cnum: 102,
        };
        let test = UriStyle { strip_path: true };
        assert_eq!(
            go_to_definition_text(test, "/a/b/Hover.res", pos),
            "\nGo to: [Type definition](Hover.res#L111,3)"
        );
    }
}
