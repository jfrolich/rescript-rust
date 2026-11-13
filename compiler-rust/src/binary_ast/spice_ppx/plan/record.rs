//! The plan of a record's codecs (`records_generate_encoder`,
//! `records_generate_decoder`, `records_generate_flat_decoder_expr`).
//!
//! ```text
//! let t_encode = v => (v => (JSON.Object(Dict.fromArray(Spice.filterOptional(
//!     [("x", Some(codec(v.x))), ...]))): JSON.t))(v)
//! let t_decode = v => (v =>
//!   switch (v: JSON.t) {
//!   | JSON.Object(dict) =>
//!     switch Option.getOr(Option.map(Dict.get(dict, "x"), codec), fallback) {
//!     | Ok(spice_field_x) => ... Ok({x: spice_field_x, ...})
//!     | Error(e: Spice.decodeError) =>
//!       Spice.error(~path="." ++ "x" ++ e.path, e.message, e.value)
//!     }
//!   | _ => Spice.error("Not an object", v)
//!   })(v)
//! ```
//!
//! Obligations are pushed in the order inference meets the names: a
//! function's body, a callee before its arguments, an annotation's type
//! before its expression, a constructor before its argument, a record
//! before its label, the scrutinee of a match, then the patterns of all its
//! cases, then their bodies. A skeleton states what the body itself fixes
//! about a name's type and leaves a variable everywhere else.

use super::*;

/// A record field, as `records_parse_decl` reads it.
#[derive(Clone, Copy)]
pub(super) struct Field {
    name: StrIdx,
    /// `@spice.key(<constant>)`.
    key: Option<ExprIdx>,
    /// `@spice.default(<constant>)`.
    default: Option<ExprIdx>,
    /// `x?: t`.
    optional: bool,
    /// `x: option<t>`.
    option: bool,
    /// The codec the field's value goes through.
    codec: Spec,
}

/// The constant expression of the attribute `name` of a label. The
/// classifier admitted the label, so a payload is one constant.
/// Cost: O(attributes of the label).
fn constant_payload(label: &LabelDeclaration, name: &str, arena: &ParseArena) -> Option<ExprIdx> {
    let attr = label
        .pld_attributes
        .iter()
        .find(|attr| arena.get_string(attr.0.txt) == name)?;
    let Payload::PStr(items) = &attr.1 else {
        unreachable!("the classifier admits constant payloads only")
    };
    let StructureItemDesc::Pstr_eval(eval) = &items[0].pstr_desc else {
        unreachable!("the classifier admits constant payloads only")
    };
    Some(eval.0)
}

/// Whether the labels of a record are ones a plan describes: at least one
/// field, and every `@spice.key` and `@spice.default` a literal constant (a
/// template without interpolation is a constant to the derive, but not one
/// expression node).
/// Cost: O(attributes of the labels); no allocation.
pub(super) fn planned(labels: &[LabelDeclaration], arena: &ParseArena) -> bool {
    !labels.is_empty()
        && labels.iter().all(|label| {
            ["spice.key", "spice.default"].iter().all(|name| {
                constant_payload(label, name, arena).is_none_or(|expr| {
                    matches!(arena.get_expr(expr).pexp_desc, ExpressionDesc::Pexp_constant(_))
                })
            })
        })
}

/// Read a field. Cost: O(attributes of the label).
pub(super) fn field(label: &LabelDeclaration, arena: &ParseArena) -> Field {
    let has = |name: &str| {
        label
            .pld_attributes
            .iter()
            .any(|attr| arena.get_string(attr.0.txt) == name)
    };
    let optional = label.pld_optional || has("ns.optional") || has("res.optional");
    let option = check_option_type(&label.pld_type, arena);
    let codec = if optional {
        Spec::Omittable(label.pld_type)
    } else if option {
        let CoreTypeDesc::Ptyp_constr((_, args)) = &arena.get_core_type(label.pld_type).ptyp_desc
        else {
            unreachable!("an option type is a constructor application")
        };
        Spec::Omittable(arena.type_list(*args)[0])
    } else {
        Spec::Type(label.pld_type, EncodeContext::Value)
    };
    Field {
        name: label.pld_name.txt,
        key: constant_payload(label, "spice.key", arena),
        default: constant_payload(label, "spice.default", arena),
        optional,
        option,
        codec,
    }
}

/// The names a record body uses, made once per binding.
pub(super) struct Names {
    pub(super) dummy: LocIdx,
    pub(super) none: LocIdx,
}

impl Names {
    /// Cost: O(1).
    pub(super) fn of(arena: &ParseArena) -> Self {
        Names {
            dummy: arena.dummy_loc(),
            none: arena.none_loc(),
        }
    }
}

/// Where an object encoder reads the values of the fields.
#[derive(Clone, Copy)]
pub(super) enum FieldValues {
    /// `v.x`: the fields of the local `local`, a record of variable `record`.
    Access { local: u32, record: u32 },
    /// The variables a record pattern bound: field `i` is the local
    /// `first_local + i`, of variable `first_var + i`.
    Locals { first_local: u32, first_var: u32 },
}

/// Per field of a record decoder: its scrutinee, its two pattern
/// constructors, the variables of its value and of its error, and its key's
/// obligation.
pub(super) struct Decoded {
    scrutinee: BodyIdx,
    ok: ObligationIdx,
    error: ObligationIdx,
    value: u32,
    failure: u32,
    key: Option<ObligationIdx>,
}

/// What the decoder of a record's fields reads and makes
/// (`records_generate_flat_decoder_expr`).
pub(super) struct Flat {
    /// The `Type` obligation of `JSON.t` the value is annotated with.
    pub(super) json: ObligationIdx,
    /// The variable of the dictionary.
    pub(super) dict: u32,
    /// The variable of the decoder's result.
    pub(super) result: u32,
    /// The variable of the record.
    pub(super) record: u32,
    /// The local holding the value decoded, which a missing field reports.
    pub(super) value_local: u32,
    /// The local holding the dictionary; the fields' are the locals after
    /// it.
    pub(super) dict_local: u32,
    /// For the inline record of a declared constructor: the constructor's
    /// name and the variable of the declared type.
    pub(super) inline: Option<(StrIdx, u32)>,
}

impl Builder<'_> {
    pub(super) fn sk(&mut self, node: SkeletonNode) -> SkeletonIdx {
        self.arena.plans_mut().push_skeleton(node)
    }

    pub(super) fn var(&mut self, var: u32) -> SkeletonIdx {
        self.sk(SkeletonNode::Var(var))
    }

    pub(super) fn string(&mut self) -> SkeletonIdx {
        self.sk(SkeletonNode::Predef {
            ty: Predef::String,
            args: 0,
        })
    }

    /// Cost: O(1), one body slot.
    pub(super) fn node(&mut self, node: BodyNode) -> BodyIdx {
        self.arena.plans_mut().push_body(node)
    }

    /// A value the derive names with the dummy location (`expr_ident_path`),
    /// used at the skeleton that starts at `skeleton`.
    /// Cost: O(path parts), one longident.
    pub(super) fn value(&mut self, parts: &[&str], skeleton: SkeletonIdx) -> BodyIdx {
        let name = lident_path_static(self.arena, parts);
        self.value_named(name, skeleton)
    }

    /// [`Builder::value`] of a longident made once per binding.
    /// Cost: O(1), one obligation and one body slot.
    pub(super) fn value_named(&mut self, name: LidentIdx, skeleton: SkeletonIdx) -> BodyIdx {
        let name_loc = self.arena.dummy_loc();
        let plans = self.arena.plans_mut();
        let obligation = plans.push_obligation(Obligation::Value {
            name,
            name_loc,
            skeleton,
            expr_loc: ExprLoc::OfName,
            called: true,
        });
        plans.push_body(BodyNode::Free(obligation))
    }

    /// The obligation of a constructor given `args` arguments, whose
    /// skeletons start at `skeleton`. Cost: O(1), one obligation slot.
    pub(super) fn constructor(
        &mut self,
        name: LidentIdx,
        of: Owner,
        ty: ObligationIdx,
        site: Site,
        args: u8,
        skeleton: SkeletonIdx,
    ) -> ObligationIdx {
        self.arena.plans_mut().push_obligation(Obligation::Constructor {
            name,
            ty,
            skeleton,
            of,
            site,
            args,
        })
    }

    /// The obligation of a label with argument `arg` and record `record`.
    /// Cost: O(1), two skeleton slots and one obligation slot.
    pub(super) fn label(
        &mut self,
        name: LidentIdx,
        usage: LabelUse,
        arg: u32,
        record: u32,
    ) -> ObligationIdx {
        let skeleton = self.var(arg);
        self.var(record);
        self.arena.plans_mut().push_obligation(Obligation::Label {
            name,
            skeleton,
            usage,
        })
    }

    /// A user's constant used at `string` (a key) or at the variable `at`.
    /// Cost: O(1), one skeleton slot and one obligation slot.
    pub(super) fn literal(&mut self, expr: ExprIdx, at: Option<u32>) -> ObligationIdx {
        let skeleton = match at {
            Some(var) => self.var(var),
            None => self.string(),
        };
        self.arena
            .plans_mut()
            .push_obligation(Obligation::Literal { expr, skeleton })
    }

    /// The key of a field: its name, or the user's constant, whose
    /// obligation is made at its first use in the binding.
    /// Cost: O(1), at most one obligation and one body slot.
    fn key(&mut self, field: &Field, obligation: &mut Option<ObligationIdx>) -> BodyIdx {
        match field.key {
            None => self.node(BodyNode::Str(field.name)),
            Some(expr) => {
                let literal = *obligation.get_or_insert_with(|| self.literal(expr, None));
                self.node(BodyNode::Literal(literal))
            }
        }
    }

    /// A total application. Cost: O(arguments).
    pub(super) fn apply(&mut self, funct: BodyIdx, args: &[BodyIdx]) -> BodyIdx {
        self.arena.plans_mut().push_apply(funct, args, false)
    }

    /// `Spice.error(message, value)` or `Spice.error(~path, message, value)`.
    /// Cost: O(arguments).
    pub(super) fn apply_error(&mut self, error: BodyIdx, args: &[BodyIdx]) -> BodyIdx {
        let plans = self.arena.plans_mut();
        let start = plans.push_args(args);
        plans.push_body(BodyNode::Apply {
            funct: error,
            args: start,
            len: args.len() as u16,
            partial: false,
            optional: if args.len() == 3 {
                OptionalArg::Supplied
            } else {
                OptionalArg::Omitted
            },
        })
    }

    /// The skeleton of `Spice.error` used with a path of type `path`; the
    /// caller pushes the skeletons of the message, the value and the result
    /// after it. Cost: O(1), three skeleton slots.
    pub(super) fn error_skeleton(&mut self, path: u32) -> SkeletonIdx {
        let label = self.arena.intern_string("path");
        let skeleton = self.sk(SkeletonNode::Arrow { params: 3 });
        self.sk(SkeletonNode::Optional(label));
        self.var(path);
        skeleton
    }

    /// Cost: O(1), one skeleton slot.
    pub(super) fn json(&mut self, json: ObligationIdx) -> SkeletonIdx {
        self.sk(SkeletonNode::Named { ty: json, args: 0 })
    }

    /// `JSON.Object(Dict.fromArray(Spice.filterOptional([(key, value)...])))`
    /// annotated with `JSON.t` (`records_generate_encoder`,
    /// `records_generate_inline_encoder_expr`): the object's node and the
    /// annotation's `Type` obligation.
    /// Cost: O(fields + codecs of their types): per field at most one label,
    /// one constructor and one literal obligation beside those of its codec,
    /// at most five body nodes beside the codec's; the fields' tuples are
    /// gathered in the item's node buffer.
    pub(super) fn object_encoder(
        &mut self,
        labels: &[LabelDeclaration],
        names: &Names,
        values: FieldValues,
    ) -> (BodyIdx, ObligationIdx) {
        let json_name = self.arena.spice_json_ctyp_lident();
        let json = self.arena.plans_mut().push_obligation(Obligation::Type {
            name: json_name,
            name_loc: names.none,
            arity: 0,
            var: NO_VAR,
        });
        let (dict, filtered, entry) = (self.fresh(), self.fresh(), self.fresh());
        let object = lident_path_static(self.arena, &["JSON", "Object"]);
        let skeleton = self.var(dict);
        self.json(json);
        let object = self.constructor(object, Owner::Type, json, Site::Construct, 1, skeleton);
        let skeleton = self.sk(SkeletonNode::Arrow { params: 1 });
        self.var(filtered);
        self.var(dict);
        let from_array = self.value(&["Dict", "fromArray"], skeleton);
        // `array<(string, 'entry)> => 'filtered`
        let skeleton = self.sk(SkeletonNode::Arrow { params: 1 });
        self.sk(SkeletonNode::Predef {
            ty: Predef::Array,
            args: 1,
        });
        self.sk(SkeletonNode::Tuple { len: 2 });
        self.string();
        self.var(entry);
        self.var(filtered);
        let filter = self.value(&["Spice", "filterOptional"], skeleton);

        let some = self.arena.intern_string("Some");
        let some = self.arena.push_lident_from_idx(some);
        let first_item = self.scratch.nodes.len();
        for (i, label) in labels.iter().enumerate() {
            let field = field(label, self.arena);
            let key = self.key(&field, &mut None);
            let value = match values {
                FieldValues::Access { .. } => self.fresh(),
                FieldValues::Locals { first_var, .. } => first_var + i as u32,
            };
            // A field that is always present is wrapped in `Some`.
            let (wrap, encoded) = if field.optional || field.option {
                (None, entry)
            } else {
                let encoded = self.fresh();
                let skeleton = self.var(encoded);
                self.var(entry);
                let no_type = ObligationIdx(0);
                let some =
                    self.constructor(some, Owner::Option, no_type, Site::Construct, 1, skeleton);
                (Some(some), encoded)
            };
            let codec = self.codec(field.codec, Slot::Applied(value, encoded));
            let read = match values {
                FieldValues::Access { local, record } => {
                    let local = self.node(BodyNode::Local(local));
                    let name = self.arena.push_lident_from_idx(field.name);
                    let label = self.label(name, LabelUse::Access, value, record);
                    self.node(BodyNode::Field {
                        record: local,
                        label,
                    })
                }
                FieldValues::Locals { first_local, .. } => {
                    self.node(BodyNode::Local(first_local + i as u32))
                }
            };
            let mut encoded = self.apply(codec, &[read]);
            if let Some(constructor) = wrap {
                encoded = self.node(BodyNode::Construct {
                    constructor,
                    arg: encoded,
                });
            }
            let plans = self.arena.plans_mut();
            let args = plans.push_args(&[key, encoded]);
            let item = plans.push_body(BodyNode::Tuple { args, len: 2 });
            self.scratch.nodes.push(item);
        }
        let plans = self.arena.plans_mut();
        let args = plans.push_args(&self.scratch.nodes[first_item..]);
        self.scratch.nodes.truncate(first_item);
        let array = plans.push_body(BodyNode::Array {
            args,
            len: labels.len() as u32,
        });
        let filtered = self.apply(filter, &[array]);
        let entries = self.apply(from_array, &[filtered]);
        let body = self.node(BodyNode::Construct {
            constructor: object,
            arg: entries,
        });
        (body, json)
    }

    /// The encoder of a record: the root of its body and its stated type.
    /// Cost: that of [`Builder::object_encoder`], and a fixed number of
    /// nodes.
    fn record_encoder(
        &mut self,
        labels: &[LabelDeclaration],
        names: &Names,
    ) -> (BodyIdx, SkeletonIdx) {
        let record = self.fresh();
        let (body, json) =
            self.object_encoder(labels, names, FieldValues::Access { local: 1, record });
        let param = self.arena.spice_field_v();
        let root = self.eta(body, param);
        let stated = self.sk(SkeletonNode::Arrow { params: 1 });
        self.var(record);
        self.json(json);
        (root, stated)
    }

    /// `v => (v => body)(v)`, as `generate_codec_decls` wraps a codec whose
    /// own parameter is `inner_param`. Cost: O(1), five body nodes.
    pub(super) fn eta(&mut self, body: BodyIdx, inner_param: StrIdx) -> BodyIdx {
        let outer_param = self.arena.spice_runtime_v();
        let inner = self.node(BodyNode::Function {
            param: inner_param,
            body,
        });
        let local = self.node(BodyNode::Local(0));
        let applied = self.apply(inner, &[local]);
        self.node(BodyNode::Function {
            param: outer_param,
            body: applied,
        })
    }

    /// The decoder of a record's fields, the body of the case
    /// `JSON.Object(dict)` (`records_generate_flat_decoder_expr`): the
    /// matches on each field's result, innermost making `Ok` of the record.
    /// Cost: O(fields + codecs of their types): per field at most sixteen
    /// obligations beside those of its codec; the per-field state is held in
    /// the item's decoder buffer.
    pub(super) fn flat_decoder(
        &mut self,
        labels: &[LabelDeclaration],
        names: &Names,
        flat: &Flat,
    ) -> BodyIdx {
        let lident = |arena: &mut ParseArena, name: &str| {
            let name = arena.intern_string(name);
            arena.push_lident_from_idx(name)
        };
        let ok = lident(self.arena, "Ok");
        let error_name = lident(self.arena, "Error");
        let none = lident(self.arena, "None");
        let decode_error = lident_path_parse(self.arena, &["Spice", "decodeError"]);
        let (missing, dot) = (
            self.arena.intern_string(" missing"),
            self.arena.intern_string("."),
        );
        let no_type = ObligationIdx(0);
        let (json, dict, result, record) = (flat.json, flat.dict, flat.result, flat.record);
        let fields_local = flat.dict_local + 1;

        let first_decoded = self.scratch.decoded.len();
        for label in labels {
            let field = field(label, self.arena);
            let (found, mapped, fallback, scrutinee) =
                (self.fresh(), self.fresh(), self.fresh(), self.fresh());
            let mut key_obligation = None;
            let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
            self.var(mapped);
            self.var(fallback);
            self.var(scrutinee);
            let get_or = self.value(&["Option", "getOr"], skeleton);
            let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
            self.var(found);
            let slot = self.arg_slot(field.codec);
            self.var(mapped);
            let map = self.value(&["Option", "map"], skeleton);
            let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
            self.var(dict);
            self.string();
            self.var(found);
            let get = self.value(&["Dict", "get"], skeleton);
            let dict_local = self.node(BodyNode::Local(flat.dict_local));
            let key = self.key(&field, &mut key_obligation);
            let got = self.apply(get, &[dict_local, key]);
            let codec = self.codec(field.codec, slot);
            let mapped_value = self.apply(map, &[got, codec]);

            let absent = field.optional || field.option;
            let fallback_value = if field.default.is_some() || absent {
                // `Ok(default)` or `Ok(None)`.
                let inner = self.fresh();
                let skeleton = self.var(inner);
                self.var(fallback);
                let ok =
                    self.constructor(ok, Owner::Result, no_type, Site::Construct, 1, skeleton);
                let arg = match field.default {
                    Some(default) => {
                        let literal = self.literal(default, Some(inner));
                        self.node(BodyNode::Literal(literal))
                    }
                    None => {
                        let skeleton = self.var(inner);
                        let none = self.constructor(
                            none,
                            Owner::Option,
                            no_type,
                            Site::Construct,
                            0,
                            skeleton,
                        );
                        self.node(BodyNode::Construct {
                            constructor: none,
                            arg: BodyIdx(0),
                        })
                    }
                };
                self.node(BodyNode::Construct {
                    constructor: ok,
                    arg,
                })
            } else {
                // `Spice.error(key ++ " missing", v)`.
                let (path, message) = (self.fresh(), self.fresh());
                let skeleton = self.error_skeleton(path);
                self.var(message);
                self.json(json);
                self.var(fallback);
                let error = self.value(&["Spice", "error"], skeleton);
                let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
                self.string();
                self.string();
                self.var(message);
                let concat = self.value(&["++"], skeleton);
                let key = self.key(&field, &mut key_obligation);
                let missing = self.node(BodyNode::Str(missing));
                let message = self.apply(concat, &[key, missing]);
                let v = self.node(BodyNode::Local(flat.value_local));
                self.apply_error(error, &[message, v])
            };
            let scrutinee_node = self.apply(get_or, &[mapped_value, fallback_value]);

            let (value, failure) = (self.fresh(), self.fresh());
            let skeleton = self.var(value);
            self.var(scrutinee);
            let ok_pattern =
                self.constructor(ok, Owner::Result, no_type, Site::Pattern, 1, skeleton);
            let skeleton = self.var(failure);
            self.var(scrutinee);
            let error_pattern =
                self.constructor(error_name, Owner::Result, no_type, Site::Pattern, 1, skeleton);
            self.arena.plans_mut().push_obligation(Obligation::Type {
                name: decode_error,
                name_loc: names.none,
                arity: 0,
                var: failure,
            });
            self.scratch.decoded.push(Decoded {
                scrutinee: scrutinee_node,
                ok: ok_pattern,
                error: error_pattern,
                value,
                failure,
                key: key_obligation,
            });
        }

        // `Ok({x: spice_field_x, ...})`, or `Ok(C({x: spice_field_x, ...}))`
        // for the inline record of the declared constructor `C`.
        let (made, usage) = match flat.inline {
            None => (record, LabelUse::Construct),
            Some((_, declared)) => (declared, LabelUse::ConstructInline),
        };
        let skeleton = self.var(made);
        self.var(result);
        let ok = self.constructor(ok, Owner::Result, no_type, Site::Construct, 1, skeleton);
        let inline = flat.inline.map(|(name, declared)| {
            let name = self.arena.push_lident_from_idx(name);
            let skeleton = self.var(record);
            self.var(declared);
            self.constructor(name, Owner::Declared, no_type, Site::ConstructNone, 1, skeleton)
        });
        let first_label = self.arena.plans().next_obligation();
        for (i, label) in labels.iter().enumerate() {
            let name = self.arena.push_lident_from_idx(label.pld_name.txt);
            let value = self.scratch.decoded[first_decoded + i].value;
            self.label(name, usage, value, record);
        }
        let first_value = self.scratch.nodes.len();
        for i in 0..labels.len() as u32 {
            let value = self.node(BodyNode::Local(fields_local + i));
            self.scratch.nodes.push(value);
        }
        let plans = self.arena.plans_mut();
        let args = plans.push_args(&self.scratch.nodes[first_value..]);
        self.scratch.nodes.truncate(first_value);
        let mut made = plans.push_body(BodyNode::Record {
            labels: first_label,
            fields: args,
            len: labels.len() as u32,
        });
        if let Some(constructor) = inline {
            made = self.node(BodyNode::Construct {
                constructor,
                arg: made,
            });
        }
        let mut body = self.node(BodyNode::Construct {
            constructor: ok,
            arg: made,
        });

        // The matches, innermost first: each wraps the body of the fields
        // after it and has the error case of its own field.
        let (path_name, message_name, value_name) = (
            lident(self.arena, "path"),
            lident(self.arena, "message"),
            lident(self.arena, "value"),
        );
        let e = self.arena.intern_string("e");
        for (i, label) in labels.iter().enumerate().rev() {
            let field = field(label, self.arena);
            let (path, message, value, nested, inner) =
                (self.fresh(), self.fresh(), self.fresh(), self.fresh(), self.fresh());
            let skeleton = self.error_skeleton(path);
            self.var(message);
            self.var(value);
            self.var(result);
            let error = self.value(&["Spice", "error"], skeleton);
            let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
            self.string();
            self.var(nested);
            self.var(path);
            let outer = self.value(&["++"], skeleton);
            let dot = self.node(BodyNode::Str(dot));
            let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
            self.string();
            self.var(inner);
            self.var(nested);
            let concat = self.value(&["++"], skeleton);
            let mut key_obligation = self.scratch.decoded[first_decoded + i].key;
            let key = self.key(&field, &mut key_obligation);
            let failure_var = self.scratch.decoded[first_decoded + i].failure;
            // In the error case the binders are those of the fields before.
            let failure = BodyNode::Local(fields_local + i as u32);
            let access = |builder: &mut Self, name, arg| {
                let record = builder.node(failure);
                let label = builder.label(name, LabelUse::AccessDummy, arg, failure_var);
                builder.node(BodyNode::Field { record, label })
            };
            let error_path = access(self, path_name, inner);
            let nested_path = self.apply(concat, &[key, error_path]);
            let full_path = self.apply(outer, &[dot, nested_path]);
            let error_message = access(self, message_name, message);
            let error_value = access(self, value_name, value);
            let failed = self.apply_error(error, &[full_path, error_message, error_value]);

            let decoded = &self.scratch.decoded[first_decoded + i];
            let (scrutinee, ok_pattern, error_pattern) =
                (decoded.scrutinee, decoded.ok, decoded.error);
            let binder = field_var(self.arena, field.name);
            let plans = self.arena.plans_mut();
            let cases = plans.push_cases(&[
                Case {
                    pattern: CasePattern::Construct {
                        constructor: ok_pattern,
                        binder,
                    },
                    body,
                },
                Case {
                    pattern: CasePattern::Construct {
                        constructor: error_pattern,
                        binder: e,
                    },
                    body: failed,
                },
            ]);
            body = plans.push_body(BodyNode::Switch {
                scrutinee,
                cases,
                len: 2,
            });
        }
        self.scratch.decoded.truncate(first_decoded);
        body
    }

    /// `switch (v: JSON.t) { | JSON.Object(dict) => fields | _ =>
    /// Spice.error("Not an object", v) }` of the local `value_local`, whose
    /// type is the variable `value_var` (`records_generate_decoder`, and the
    /// payload of an inline record in `variants_generate_decoder_case`).
    /// `json` is the annotation's `Type` obligation, already pushed.
    /// Cost: that of [`Builder::flat_decoder`] and a fixed number of nodes.
    pub(super) fn object_decoder(
        &mut self,
        labels: &[LabelDeclaration],
        names: &Names,
        json: ObligationIdx,
        result: u32,
        value_local: u32,
        inline: Option<(StrIdx, u32)>,
    ) -> BodyIdx {
        let (dict, record) = (self.fresh(), self.fresh());
        let object = lident_path_static(self.arena, &["JSON", "Object"]);
        let skeleton = self.var(dict);
        self.json(json);
        let object = self.constructor(object, Owner::Type, json, Site::PatternDummy, 1, skeleton);
        let flat = Flat {
            json,
            dict,
            result,
            record,
            value_local,
            dict_local: value_local + 1,
            inline,
        };
        let body = self.flat_decoder(labels, names, &flat);

        // `| _ => Spice.error("Not an object", v)`.
        let path = self.fresh();
        let skeleton = self.error_skeleton(path);
        self.string();
        self.json(json);
        self.var(result);
        let error = self.value(&["Spice", "error"], skeleton);
        let not_object = self.arena.intern_string("Not an object");
        let not_object = self.node(BodyNode::Str(not_object));
        let v = self.node(BodyNode::Local(value_local));
        let otherwise = self.apply_error(error, &[not_object, v]);

        let scrutinee = self.node(BodyNode::Local(value_local));
        let dict_binder = self.arena.intern_string("dict");
        let plans = self.arena.plans_mut();
        let cases = plans.push_cases(&[
            Case {
                pattern: CasePattern::Construct {
                    constructor: object,
                    binder: dict_binder,
                },
                body,
            },
            Case {
                pattern: CasePattern::Any,
                body: otherwise,
            },
        ]);
        plans.push_body(BodyNode::Switch {
            scrutinee,
            cases,
            len: 2,
        })
    }

    /// The `Type` obligation of the decoders' annotation `(v: JSON.t)`
    /// (`ctyp_json_t`), of the value of variable `var` or of nothing
    /// ([`NO_VAR`]). Cost: O(1), one longident and one obligation.
    pub(super) fn decoder_json(&mut self, names: &Names, var: u32) -> ObligationIdx {
        let json_name = {
            let (json, t) = (self.arena.spice_json_str(), self.arena.spice_json_t_str());
            lident_path_from_parts(self.arena, &[json, t])
        };
        self.arena.plans_mut().push_obligation(Obligation::Type {
            name: json_name,
            name_loc: names.dummy,
            arity: 0,
            var,
        })
    }

    /// The decoder of a record: the root of its body and its stated type.
    /// Cost: that of [`Builder::object_decoder`].
    fn record_decoder(
        &mut self,
        labels: &[LabelDeclaration],
        names: &Names,
    ) -> (BodyIdx, SkeletonIdx) {
        let json = self.decoder_json(names, NO_VAR);
        let result = self.fresh();
        let body = self.object_decoder(labels, names, json, result, 1, None);
        let param = self.arena.spice_field_v();
        let root = self.eta(body, param);
        let stated = self.sk(SkeletonNode::Arrow { params: 1 });
        self.json(json);
        self.var(result);
        (root, stated)
    }
}

/// Append the bindings of a declaration whose bodies `body` builds:
/// `<type>_encode`, `<type>_encodeJson` (the same encoder) and
/// `<type>_decode`, each with a stated type.
/// Cost: that of `body` per binding, and one name per binding.
pub(super) fn stated_bindings(
    arena: &mut ParseArena,
    type_name: &str,
    settings: GeneratorSettings,
    scratch: &mut Scratch,
    mut body: impl FnMut(&mut Builder<'_>) -> (BodyIdx, SkeletonIdx),
) {
    let mut binding = |arena: &mut ParseArena, suffix: &str, side: Side, attributes: Attributes| {
        let first = arena.plans().next_obligation();
        let mut builder = Builder {
            arena,
            side,
            vars: 0,
            scratch: &mut *scratch,
        };
        let (body, stated) = body(&mut builder);
        let vars = builder.vars;
        let name = arena.push_string(format!("{type_name}{suffix}"));
        let plans = arena.plans_mut();
        let obligations = Span {
            start: first.0,
            len: plans.next_obligation().0 - first.0,
        };
        plans.push_binding(Binding {
            name,
            attributes,
            obligations,
            body,
            vars,
            ty: TypeSource::Stated(stated),
        });
    };
    if settings.do_encode {
        binding(arena, ENCODER_FUNC_SUFFIX, Side::Encode, Attributes::new());
        let attributes = vec![unused_value_warning_attribute(arena)].into();
        binding(arena, VALUE_ENCODER_FUNC_SUFFIX, Side::Encode, attributes);
    }
    if settings.do_decode {
        binding(arena, DECODER_FUNC_SUFFIX, Side::Decode, Attributes::new());
    }
}

/// Append the bindings of a record declaration.
/// Cost: O(fields + codecs of their types) per binding.
pub(super) fn bindings(
    arena: &mut ParseArena,
    type_name: &str,
    labels: &[LabelDeclaration],
    settings: GeneratorSettings,
    scratch: &mut Scratch,
) {
    let names = Names::of(arena);
    stated_bindings(arena, type_name, settings, scratch, |builder| match builder.side {
        Side::Encode => builder.record_encoder(labels, &names),
        Side::Decode => builder.record_decoder(labels, &names),
    });
}
