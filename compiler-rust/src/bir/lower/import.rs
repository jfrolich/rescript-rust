//! Dynamic imports and the awaited-unit fact used by flat make reads.
use super::*;
use crate::bir::j::plain;
use crate::bir::{ImportId, VarSpan};
use crate::lambda::{
    LamLoc,
    lam_primitive::{ImportSource, Primitive},
};
use crate::types::external_ffi_types::{ExternalModuleName, ModuleBindName};

impl State {
    /// M: is_awaited_unit / awaited_units. O(1), inspect two primitive headers
    /// at the binding on the existing walk; no second unit traversal.
    pub(super) fn record_awaited_unit(&mut self, var: VarId, value: NodeId) {
        let View::Prim {
            primitive,
            args: [import],
        } = self.source.view(value)
        else {
            return;
        };
        if !matches!(self.arena.primitive(primitive).primitive, Primitive::Pawait) {
            return;
        }
        let View::Prim { primitive, .. } = self.source.view(*import) else {
            return;
        };
        if matches!(&self.arena.primitive(primitive).primitive, Primitive::Pimport(source)
            if matches!(source.as_ref(), ImportSource::ImportModule { path, .. } if path.is_empty()))
        {
            self.awaited_units[var.index()] = true;
        }
    }

    /// X: static_index. O(name bytes), one plain member node.
    pub(super) fn static_member(&mut self, object: NodeId, name: &str) -> NodeId {
        let property = self.arena.intern_text(name);
        plain::node(
            &mut self.arena,
            View::JDot {
                object,
                property,
                position: crate::js_ir::arena::FieldPos::new(None),
            },
            0,
        )
    }

    /// X: import_of_path. O(path bytes), one global and one call.
    fn import_of_path(&mut self, path: &str) -> NodeId {
        let var = self.fresh_variable("import");
        self.arena.mark_js_global(var);
        self.idents[var.index()] = Ident::create_persistent("import");
        let callee = self.pure_expression(View::Var { var }, 0);
        let text = self.arena.intern_text(path);
        let path = plain::node(&mut self.arena, View::JStr { text }, 0);
        self.call_node(callee, &[path], Default::default())
    }

    /// X: wrap_then_path. O(path segments + spelling bytes). The callback
    /// owns one parameter and a linear member chain, with no subtree copy.
    fn wrap_then_path(&mut self, import: NodeId, path: &[String]) -> NodeId {
        let param = self.fresh_variable("m");
        let mut value = self.pure_expression(View::Var { var: param }, 0);
        for segment in path {
            self.primitive_steps += 1;
            value = self.static_member(value, segment);
        }
        let ret = plain::node(&mut self.arena, View::SReturn { value }, 0);
        let body = plain::node(&mut self.arena, View::SBlock { statements: &[ret] }, 0);
        let header = self.arena.function_header(
            VarSpan {
                start: param.0,
                len: 1,
            },
            Default::default(),
            LamLoc::NONE,
        );
        let callback = self.pure_expression(View::JFun { body, header }, 0);
        let then = self.static_member(import, "then");
        self.call_node(then, &[callback], Default::default())
    }

    /// X: external_module_id. O(m + bundle/hint bytes) for m imports. No
    /// source index exists for external bundle/default pairs; reuse the first
    /// binding by scanning the small per-unit module inventory.
    pub(super) fn external_module(
        &mut self,
        external: &ExternalModuleName,
        default: bool,
        dynamic: bool,
    ) -> ImportId {
        let existing = self.arena.pools.j_modules.iter().find(|module| matches!(&module.kind,
            crate::js_ir::Kind::External { name, default: d, .. } if name == &external.bundle && *d == default)).map(|m| m.id);
        let id = existing.unwrap_or_else(|| {
            let name = external_binding_name(external);
            let var = self.fresh_variable(&name);
            self.idents[var.index()]
        });
        let module = crate::js_ir::ModuleId {
            id,
            kind: crate::js_ir::Kind::External {
                name: external.bundle.clone(),
                default,
                import_attributes: external
                    .import_attributes
                    .clone()
                    .map(|entries| crate::js_ir::op::ImportAttributes { entries }),
            },
            dynamic_import: dynamic,
        };
        self.add_import_module(module)
    }

    /// X: external_module_id / compile_import. O(1) amortized plus module
    /// spelling bytes; source imports and J module metadata stay index-aligned.
    fn add_import_module(&mut self, module: crate::js_ir::ModuleId) -> ImportId {
        let id = ImportId(self.arena.pools.imports.len() as u32);
        let path = self.arena.intern_text(module.id.name());
        self.arena.pools.imports.push(crate::bir::Import {
            name: module.id.name_atom(),
            path,
        });
        self.arena.pools.j_modules.push(module);
        self.module_constants.push(ModuleConstants::Unread);
        id
    }

    /// X: compile_import. O(module inventory + path segments + spelling bytes).
    /// Invalid paths yield undefined as in the legacy emitter; diagnostics are
    /// still emitted by the legacy side of the shared check-mode pipeline.
    pub(super) fn compile_import(&mut self, source: &ImportSource) -> NodeId {
        match source {
            ImportSource::ImportModule { module_, path } => {
                let module = crate::js_ir::ModuleId {
                    id: *module_,
                    kind: crate::js_ir::Kind::Ml,
                    dynamic_import: true,
                };
                let resolved = self
                    .resolver
                    .as_ref()
                    .and_then(|r| r.resolve_module_path(&module));
                self.dynamic_imports.push(module);
                let Some(resolved) = resolved else {
                    return plain::node(&mut self.arena, View::JUndefined, 0);
                };
                let import = self.import_of_path(&resolved);
                match path.as_slice() {
                    [] => import,
                    [name] => {
                        self.wrap_then_path(import, &[crate::js_ir::printer::js_export_name(name)])
                    }
                    _ => match crate::lambda::flat_make_name(path) {
                        Some(name) => self.wrap_then_path(
                            import,
                            &[crate::js_ir::printer::js_export_name(&name)],
                        ),
                        None => {
                            self.arena.release(import);
                            plain::node(&mut self.arena, View::JUndefined, 0)
                        }
                    },
                }
            }
            ImportSource::ImportExternal { module_, path } => {
                let module = self.external_module(module_, path.as_slice() == ["default"], true);
                self.dynamic_imports
                    .push(self.arena.pools.j_modules[module.index()].clone());
                let import = self.import_of_path(&module_.bundle);
                if path.is_empty() {
                    import
                } else {
                    self.wrap_then_path(import, path)
                }
            }
        }
    }
}

/// X: external_module_ident_name / js_id_name_of_hint_name / collect_start /
/// collect_next. O(hint bytes); one output string per distinct module binding.
fn external_binding_name(module: &ExternalModuleName) -> String {
    /// O(s.len()), copy and uppercase the first ASCII character.
    fn capitalize(s: &str) -> String {
        let mut chars = s.chars();
        let mut result = String::with_capacity(s.len());
        if let Some(c) = chars.next() {
            result.push(c.to_ascii_uppercase());
            result.push_str(chars.as_str());
        }
        result
    }
    if let ModuleBindName::PhintName(hint) = &module.module_bind_name {
        return capitalize(hint);
    }
    let name = &module.bundle;
    let offset = name.rfind('/').map_or(0, |i| i + 1);
    let suffix = &name[offset..];
    if suffix
        .as_bytes()
        .first()
        .is_some_and(u8::is_ascii_alphabetic)
        && suffix
            .bytes()
            .skip(1)
            .all(|c| c.is_ascii_alphanumeric() || c == b'_')
    {
        return capitalize(suffix);
    }
    let mut result = String::new();
    let mut start = true;
    for c in suffix.bytes() {
        if start {
            if c.is_ascii_alphabetic() {
                result.push((c as char).to_ascii_uppercase());
                start = false;
            }
        } else if c.is_ascii_alphanumeric() || c == b'_' {
            result.push(c as char);
        } else if c == b'.' || c == b'-' {
            start = true;
        }
    }
    if result.is_empty() {
        if offset == 0 {
            name.clone()
        } else {
            capitalize(name)
        }
    } else {
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{FieldDbgInfo, arena::LamArena};

    #[test]
    fn import_module_and_value_paths_all_continuations() {
        for path in [
            vec![],
            vec!["value".into()],
            vec!["A".into(), "make".into()],
        ] {
            let mut a = LamArena::new();
            let source = ImportSource::ImportExternal {
                module_: ExternalModuleName {
                    bundle: "example".into(),
                    module_bind_name: ModuleBindName::PhintNothing,
                    import_attributes: None,
                },
                path,
            };
            let root = a.prim_raw(Primitive::Pimport(Box::new(source)), &[], LamLoc::NONE);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn resolved_module_and_flat_value_imports_match_legacy() {
        let resolver = crate::js_ir::ModulePathResolver::from_compile_options(
            None, None, None, None, None, None, false,
        );
        for path in [
            vec![],
            vec!["default".into()],
            vec!["A".into(), "make".into()],
            vec!["A".into(), "invalid".into()],
        ] {
            let mut a = LamArena::new();
            let source = ImportSource::ImportModule {
                module_: Ident::create_persistent("Other"),
                path,
            };
            let root = a.prim_raw(Primitive::Pimport(Box::new(source)), &[], LamLoc::NONE);
            super::super::oracle_tests::compare_with_resolver(a, root, Some(&resolver));
        }
    }

    #[test]
    fn ten_thousand_import_path_segments_are_linear() {
        let mut a = LamArena::new();
        let source = ImportSource::ImportExternal {
            module_: ExternalModuleName {
                bundle: "example".into(),
                module_bind_name: ModuleBindName::PhintNothing,
                import_attributes: None,
            },
            path: vec!["field".into(); 10_000],
        };
        let root = a.prim_raw(Primitive::Pimport(Box::new(source)), &[], LamLoc::NONE);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let out = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 1);
        assert_eq!(state.primitive_steps, 10_001);
        let lowered = state.complete(Cx::value(), out);
        assert_eq!(lowered.dynamic_imports.len(), 1);
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
    }

    #[test]
    fn awaited_unit_flat_make_and_invalid_import_match_legacy() {
        // No resolver: both lowerings emit undefined and the legacy side owns
        // the diagnostic. The syntactic awaited-unit fact still holds.
        for field in ["make", "other"] {
            let mut a = LamArena::new();
            let id = Ident::new("unit", 10, IdentFlags::NONE);
            let source = ImportSource::ImportModule {
                module_: Ident::create_persistent("Other"),
                path: vec![],
            };
            let import = a.prim_raw(Primitive::Pimport(Box::new(source)), &[], LamLoc::NONE);
            let value = a.prim_raw(Primitive::Pawait, &[import], LamLoc::NONE);
            let base = a.var(id);
            let inner = a.prim_raw(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: crate::name::Name::new("Inner"),
                    },
                ),
                &[base],
                LamLoc::NONE,
            );
            let body = a.prim_raw(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: crate::name::Name::new(field),
                    },
                ),
                &[inner],
                LamLoc::NONE,
            );
            let root = a.let_(LetKind::Strict, id, value, body);
            super::super::oracle_tests::compare(a, root);
        }
    }
}
