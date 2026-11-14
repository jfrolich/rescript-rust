//! Dynamic imports and the awaited-unit fact used by flat make reads.
use super::*;
use crate::bir::j::plain;
use crate::bir::{ImportId, VarSpan};
use crate::lambda::{
    LamLoc,
    lam_primitive::{ImportSource, Primitive},
};
use crate::types::external_ffi_types::{ExternalModuleName, ModuleBindName};

#[derive(Default)]
pub(super) struct Storage {
    /// Full serialized module identity has no handle until interning assigns one.
    index: hashbrown::HashTable<(u64, ImportId, u32, u32)>,
    keys: Vec<u8>,
    key: Vec<u8>,
    binding: String,
    flat: String,
    export: String,
    /// Persistent Ident stamps are external identities, not dense unit-local handles.
    resolved: std::collections::HashMap<Ident, (ImportId, Option<crate::bir::StrId>)>,
}

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
    fn import_of_path(&mut self, text: crate::bir::StrId) -> NodeId {
        let var = self.fresh_variable("import");
        self.arena.mark_js_global(var);
        self.idents[var.index()] = Ident::create_persistent("import");
        let callee = self.pure_expression(View::Var { var }, 0);
        let path = plain::node(&mut self.arena, View::JStr { text }, 0);
        self.call_node(callee, &[path], Default::default())
    }

    /// X: wrap_then_path. O(path segments + spelling bytes). The callback
    /// owns one parameter and a linear member chain, with no subtree copy.
    fn wrap_then_path<'a>(&mut self, import: NodeId, path: impl IntoIterator<Item = &'a str>) -> NodeId {
        // `import` stays outside the callback: nothing is adopted.
        super::names::open(&mut self.arena);
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
        super::names::close(&mut self.arena, &self.idents, header);
        let then = self.static_member(import, "then");
        self.call_node(then, &[callback], Default::default())
    }

    /// X:581 external_module_id. O(bundle/hint bytes) on first encounter,
    /// then a dense lookup by interned bundle and default-import bit. All
    /// static and dynamic references share this binding table.
    pub(super) fn external_module(
        &mut self,
        external: &ExternalModuleName,
        default: bool,
        dynamic: bool,
    ) -> ImportId {
        self.external_module_parts(
            &external.bundle,
            &external.module_bind_name,
            external.import_attributes.as_deref(),
            default,
            dynamic,
        )
    }

    /// O(bundle/hint/attribute bytes) for new module metadata; spelling is borrowed.
    pub(super) fn external_module_parts(
        &mut self,
        bundle: &str,
        hint: &ModuleBindName,
        attributes: Option<&[(String, String)]>,
        default: bool,
        dynamic: bool,
    ) -> ImportId {
        let bundle_id = self.arena.intern_text(bundle);

        if self.external_bindings.len() <= bundle_id.index() {
            self.external_bindings
                .resize(bundle_id.index() + 1, [None; 2]);
        }
        let var = match self.external_bindings[bundle_id.index()][usize::from(default)] {
            Some(var) => var,
            None => {
                let mut name = std::mem::take(&mut self.import_storage.binding);
                external_binding_name_into(bundle, hint, &mut name);
                let var = self.fresh_variable(&name);
                name.clear(); self.import_storage.binding = name;
                self.external_bindings[bundle_id.index()][usize::from(default)] = Some(var);
                var
            }
        };
        let id = self.idents[var.index()];
        let mut key = std::mem::take(&mut self.import_storage.key);
        crate::binser::to_vec_reuse(&(id, bundle, attributes, default, dynamic), &mut key).expect("external module key");
        let hash = std::hash::BuildHasher::hash_one(&self.arena.pools.hash_builder, &key);
        let result = if let Some(&(_, module, _, _)) = self.import_storage.index.find(hash, |&(_, _, start, len)| {
            self.import_storage.keys[start as usize..(start + len) as usize] == key
        }) { module } else {
            let module = crate::js_ir::ModuleId {
                id,
                kind: crate::js_ir::Kind::External {
                    name: bundle.to_owned(), default,
                    import_attributes: attributes.map(|entries| crate::js_ir::op::ImportAttributes { entries: entries.to_vec() }),
                },
                dynamic_import: dynamic,
            };
            let module = self.add_import_module(module);
            let start = self.import_storage.keys.len() as u32;
            self.import_storage.keys.extend_from_slice(&key);
            self.import_storage.index.insert_unique(hash, (hash, module, start, key.len() as u32), |entry| entry.0);
            module
        };
        key.clear(); self.import_storage.key = key;
        result
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
                let (module, resolved) = if let Some(&cached) = self.import_storage.resolved.get(module_) { cached } else {
                    let module = crate::js_ir::ModuleId { id: *module_, kind: crate::js_ir::Kind::Ml, dynamic_import: true };
                    let resolved = self.resolver.as_ref().and_then(|r| r.resolve_module_path(&module));
                    let resolved = resolved.map(|path| self.arena.intern_text(&path));
                    let module = self.add_import_module(module);
                    self.import_storage.resolved.insert(*module_, (module, resolved));
                    (module, resolved)
                };
                self.dynamic_imports.push(module);
                let Some(resolved) = resolved else { return plain::node(&mut self.arena, View::JUndefined, 0) };
                let import = self.import_of_path(resolved);
                if path.is_empty() { return import; }
                let mut flat = std::mem::take(&mut self.import_storage.flat);
                let mut export = std::mem::take(&mut self.import_storage.export);
                let name = match path.as_slice() {
                    [name] => Some(name.as_str()),
                    [_, _, ..] if path.last().is_some_and(|last| last == "make") => {
                        super::flat_export_name_into(path.iter().map(String::as_str), &mut flat);
                        Some(flat.as_str())
                    }
                    _ => None,
                };
                let result = if let Some(name) = name {
                    if name == "default" { export.push_str(name); }
                    else { crate::js_ir::printer::convert_ident_into(name, &mut export); }
                    self.wrap_then_path(import, std::iter::once(export.as_str()))
                } else { self.arena.release(import); plain::node(&mut self.arena, View::JUndefined, 0) };
                flat.clear(); export.clear(); self.import_storage.flat = flat; self.import_storage.export = export;
                result
            }
            ImportSource::ImportExternal { module_, path } => {
                let module = self.external_module(module_, path.as_slice() == ["default"], true);
                self.dynamic_imports.push(module);
                let bundle = self.arena.intern_text(&module_.bundle);
                let import = self.import_of_path(bundle);
                if path.is_empty() {
                    import
                } else {
                    self.wrap_then_path(import, path.iter().map(String::as_str))
                }
            }
        }
    }
}

/// X: external_module_ident_name / js_id_name_of_hint_name / collect_start /
/// collect_next. O(hint bytes); one output string per distinct module binding.
fn external_binding_name_into(name: &str, hint: &ModuleBindName, result: &mut String) {
    /// Cost: O(B): decodes the first character, appends its ASCII uppercase form and copies
    /// the remaining B bytes to the caller buffer.
    fn capitalize(s: &str, result: &mut String) {
        let mut chars = s.chars();
        if let Some(c) = chars.next() { result.push(c.to_ascii_uppercase()); result.push_str(chars.as_str()); }
    }
    result.clear();
    if let ModuleBindName::PhintName(hint) = hint { capitalize(hint, result); return; }
    let offset = name.rfind('/').map_or(0, |i| i + 1);
    let suffix = &name[offset..];
    if suffix.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
        && suffix.bytes().skip(1).all(|c| c.is_ascii_alphanumeric() || c == b'_') {
        capitalize(suffix, result); return;
    }
    let mut start = true;
    for c in suffix.bytes() {
        if start {
            if c.is_ascii_alphabetic() { result.push((c as char).to_ascii_uppercase()); start = false; }
        } else if c.is_ascii_alphanumeric() || c == b'_' { result.push(c as char); }
        else if c == b'.' || c == b'-' { start = true; }
    }
    if result.is_empty() { if offset == 0 { result.push_str(name); } else { capitalize(name, result); } }
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
    fn external_metadata_identity_includes_attributes_and_import_flags() {
        let mut a = LamArena::new(); let root = a.const_(crate::lambda::lam_constant::Constant::JsNull);
        let mut state = State::new(crate::bir::bridge::import_lambda(&a, root).unwrap());
        let attrs = [("type".into(), "json".into())];
        let first = state.external_module_parts("example", &ModuleBindName::PhintNothing, Some(&attrs), false, true);
        let repeated = state.external_module_parts("example", &ModuleBindName::PhintName("ignoredLaterHint".into()), Some(&attrs), false, true);
        assert_eq!(first, repeated);
        for (attributes, default, dynamic) in [(None, false, true), (Some(&attrs[..]), true, true), (Some(&attrs[..]), false, false)] {
            let other = state.external_module_parts("example", &ModuleBindName::PhintNothing, attributes, default, dynamic);
            assert_ne!(first, other);
        }
    }

    #[test]
    fn unusual_external_binding_spellings_match_legacy() {
        for bundle in ["foo-bar.js", "@scope/123", "123", "é"] {
            for hint in [ModuleBindName::PhintNothing, ModuleBindName::PhintName("éxample".into())] {
                let mut a = LamArena::new();
                let root = a.prim_raw(Primitive::Pimport(Box::new(ImportSource::ImportExternal {
                    module_: ExternalModuleName { bundle: bundle.into(), module_bind_name: hint, import_attributes: None }, path: vec![],
                })), &[], LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn ten_thousand_imports_share_metadata_without_allocations() {
        for external in [true, false] {
            let mut resolver = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
            resolver.set_module_path_override("Other", "./Other.res.js".into());
            let source = if external { ImportSource::ImportExternal {
                module_: ExternalModuleName { bundle: "@scope/strange-module.json".into(), module_bind_name: ModuleBindName::PhintNothing,
                    import_attributes: Some(vec![("type".into(), "json".into())]) }, path: vec!["one".into(), "two".into()],
            } } else { ImportSource::ImportModule { module_: Ident::create_persistent("Other"), path: vec!["Inner-Name".into(), "make".into()] } };
            let mut a = LamArena::new();
            let imports: Vec<_> = (0..10_000).map(|_| a.prim_raw(Primitive::Pimport(Box::new(source.clone())), &[], LamLoc::NONE)).collect();
            let root = a.prim_raw(Primitive::Pmakearray, &imports, LamLoc::NONE);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap(); let root = input.root;
            let mut state = State::new(input); state.resolver = Some(resolver);
            let run = |s: &mut State| {
                let out = s.probe(Cx::returning(), root).unwrap(); let out = s.realize(Cx::returning(), out);
                for node in s.statements.statements(out.stmts) { s.arena.release(node); }
                if let Some(value) = out.value { s.arena.release(value); }
                s.statements.kill(out.stmts);
            };
            let lists = state.arena.lists.storage_shape().0; let funcs = state.arena.vars.funcs.len();
            let attrs = state.arena.pools.attrs.len(); let infos = state.arena.pools.js.len();
            run(&mut state);
            assert_eq!(state.dynamic_imports.len(), 10_000);
            assert!(state.dynamic_imports.iter().all(|id| *id == state.dynamic_imports[0]));
            state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state.arena.vars.funcs.reserve(state.arena.vars.funcs.len() - funcs);
            state.arena.func_owners.reserve(state.arena.vars.funcs.len() - funcs);
            state.arena.pools.attrs.reserve(state.arena.pools.attrs.len() - attrs);
            state.arena.pools.js.reserve(state.arena.pools.js.len() - infos);
            state.arena.vars.j_origin.reserve(20_000); state.arena.vars.name.reserve(20_000);
            state.arena.vars.order.reserve(20_000); state.arena.vars.flags.reserve(20_000);
            state.arena.vars.uses.reserve(20_000); state.arena.vars.binder.reserve(20_000);
            state.arena.vars.fact.reserve(20_000); state.arena.vars.printed.reserve(20_000);
            state.arena.capture_binders.reserve(20_000); state.arena.bulk_binders.reserve(20_000);
            state.arena.js_scope.as_mut().unwrap().uses.reserve(20_000); state.idents.reserve(20_000);
            state.dynamic_imports.reserve(10_000); state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
            let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.arena.vars.funcs.capacity(),
                s.arena.func_owners.capacity(), s.arena.pools.attrs.capacity(), s.arena.pools.js.capacity(),
                s.arena.pools.j_modules.capacity(), s.arena.pools.imports.capacity(), s.external_bindings.capacity(),
                s.import_storage.index.capacity(), s.import_storage.keys.capacity(), s.import_storage.key.capacity(),
                s.import_storage.binding.capacity(), s.import_storage.flat.capacity(), s.import_storage.export.capacity(), s.import_storage.resolved.capacity(),
                s.dynamic_imports.capacity(), s.idents.capacity(), s.arena.js_scope.as_ref().unwrap().uses.capacity(),
                s.arena.vars.j_origin.capacity(), s.arena.vars.name.capacity(), s.arena.vars.order.capacity(), s.arena.vars.flags.capacity(),
                s.arena.vars.uses.capacity(), s.arena.vars.binder.capacity(), s.arena.vars.fact.capacity(), s.arena.vars.printed.capacity(),
                s.arena.capture_binders.capacity(), s.arena.bulk_binders.capacity(), s.argument_outputs.capacity(), s.argument_values.capacity(),
                s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity()];
            let before = capacities(&state); let free = state.free.capacities(); let stmts = state.statements.capacities();
            let visits = state.source_steps; let primitives = state.primitive_steps;
            let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
            assert_eq!(allocations.count_total, 0, "external={external} {allocations:?}");
            assert_eq!(capacities(&state), before); assert_eq!(state.free.capacities(), free); assert_eq!(state.statements.capacities(), stmts);
            assert_eq!(state.source_steps - visits, 10_001);
            assert_eq!(state.primitive_steps - primitives, if external { 40_001 } else { 30_001 });
            assert_eq!(state.dynamic_imports.len(), 20_000);
            assert!(state.import_storage.key.is_empty() && state.import_storage.binding.is_empty() && state.import_storage.flat.is_empty() && state.import_storage.export.is_empty());
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
