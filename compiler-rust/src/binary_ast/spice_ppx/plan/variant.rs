//! The plan of a variant's codecs (`variants_generate_codecs` without
//! `@spice.serde` or `@unboxed`).
//!
//! ```text
//! let t_encode = v => (v => (switch v {
//!   | C => JSON.Array([JSON.String("C")])
//!   | A(v0) => JSON.Array([JSON.String("A"), codec(v0)])
//!   | R({x: spice_field_x}) => JSON.Array([JSON.String("R"), (JSON.Object(...): JSON.t)])
//!   }: JSON.t))(v)
//! let t_decode = v => (v => switch (v: JSON.t) {
//!   | JSON.Array([]) => Spice.error("Expected variant, found empty array", v)
//!   | JSON.Array(json_arr) => switch Array.getUnsafe(json_arr, 0) {
//!     | JSON.String("A") =>
//!       if Array.length(json_arr) != 2 {
//!         Spice.error("Invalid number of arguments to variant constructor", v)
//!       } else {
//!         switch codec(Array.getUnsafe(json_arr, 1)) {
//!         | Ok(v0) => Ok(A(v0))
//!         | Error(e: Spice.decodeError) => Error({...e, path: "[1]" ++ e.path})
//!         }
//!       }
//!     | _ => Spice.error("Invalid variant constructor", Array.getUnsafe(json_arr, 0))
//!     }
//!   | _ => Spice.error("Not a variant", v)
//!   })(v)
//! ```
//!
//! With `@spice.as` on every constructor (all constant) a constructor is
//! written as its literal, `JSON.String(lit)` or `JSON.Number(lit)`, and the
//! decoder compares the string or the number with each literal in turn.
//!
//! Obligations follow the order of `record.rs`: a function's body, a callee
//! before its arguments, an annotation's type before its expression, a
//! constructor before its argument, the scrutinee of a match, the patterns of
//! all its cases, then their bodies; a record update's base, its label, then
//! its value; a condition, then its two branches.

use super::record::{FieldValues, Names};
use super::*;
use crate::binary_ast::derive::plan::{PatIdx, PatNode};

/// How a variant's constructors are written.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// `JSON.Array([JSON.String(name), args...])`.
    Array,
    /// Every constructor is constant and has a `@spice.as` literal.
    Alias,
}

/// The `@spice.as` payload of a constructor, when it has one.
/// Cost: O(attributes of the constructor); no allocation.
fn alias(constructor: &ConstructorDeclaration, arena: &ParseArena) -> Option<ExprIdx> {
    let attr = constructor
        .pcd_attributes
        .iter()
        .find(|attr| arena.get_string(attr.0.txt) == "spice.as")?;
    let Payload::PStr(items) = &attr.1 else {
        return None;
    };
    let [item] = items.as_slice() else {
        return None;
    };
    let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
        return None;
    };
    Some(eval.0)
}

/// Whether a `@spice.as` literal is a string; the classifier admitted only
/// string and float constants. Cost: O(1).
fn alias_is_string(expr: ExprIdx, arena: &ParseArena) -> bool {
    matches!(
        arena.get_expr(expr).pexp_desc,
        ExpressionDesc::Pexp_constant(Constant::String(_))
    )
}

/// Whether the constructors of a variant are ones a plan describes: at least
/// one; none with a return type; no `@spice.*` attribute but `@spice.as`, at
/// most once; either no constructor has `@spice.as` or every one has it, is
/// constant, and its payload is a string or float constant (the general path
/// reports the other cases); at most 65,535 arguments; and an inline record that
/// `record::planned` admits. The types of the arguments are classified by
/// the caller.
/// Cost: O(constructors + their attributes and labels' attributes); no
/// allocation.
pub(in crate::binary_ast) fn planned(
    constructors: &[ConstructorDeclaration],
    arena: &ParseArena,
) -> bool {
    if constructors.is_empty() {
        return false;
    }
    let mut aliased = 0;
    for constructor in constructors {
        if constructor.pcd_res.is_some() {
            return false;
        }
        let mut aliases = 0;
        for attr in &constructor.pcd_attributes {
            let name = arena.get_string(attr.0.txt);
            if name == "spice.as" {
                aliases += 1;
            } else if name.starts_with("spice.") {
                return false;
            }
        }
        if aliases > 1 {
            return false;
        }
        if aliases == 1 {
            aliased += 1;
            let Some(expr) = alias(constructor, arena) else {
                return false;
            };
            let constant = matches!(
                arena.get_expr(expr).pexp_desc,
                ExpressionDesc::Pexp_constant(Constant::String(_) | Constant::Float(..))
            );
            let constant_constructor = matches!(
                &constructor.pcd_args,
                ConstructorArguments::Pcstr_tuple(args) if args.is_empty()
            );
            if !constant || !constant_constructor {
                return false;
            }
        }
        let admitted = match &constructor.pcd_args {
            ConstructorArguments::Pcstr_tuple(args) => args.len() <= usize::from(u16::MAX),
            ConstructorArguments::Pcstr_record(labels) => record::planned(labels, arena),
        };
        if !admitted {
            return false;
        }
    }
    aliased == 0 || aliased == constructors.len()
}

/// The names a variant's bodies use, made once per binding.
struct Lids {
    json_array: LidentIdx,
    json_string: LidentIdx,
    json_number: LidentIdx,
    error: LidentIdx,
    concat: LidentIdx,
    get_unsafe: LidentIdx,
    length: LidentIdx,
    not_equal: LidentIdx,
    equal: LidentIdx,
    ok: LidentIdx,
    error_constructor: LidentIdx,
    path: LidentIdx,
    decode_error: LidentIdx,
}

impl Lids {
    /// Cost: O(1): thirteen longidents.
    fn of(arena: &mut ParseArena) -> Self {
        let lident = |arena: &mut ParseArena, name: &str| {
            let name = arena.intern_string(name);
            arena.push_lident_from_idx(name)
        };
        Lids {
            json_array: lident_path_static(arena, &["JSON", "Array"]),
            json_string: lident_path_static(arena, &["JSON", "String"]),
            json_number: lident_path_static(arena, &["JSON", "Number"]),
            error: lident_path_static(arena, &["Spice", "error"]),
            concat: lident_path_static(arena, &["++"]),
            get_unsafe: lident_path_static(arena, &["Array", "getUnsafe"]),
            length: lident_path_static(arena, &["Array", "length"]),
            not_equal: lident_path_static(arena, &["!="]),
            equal: lident_path_static(arena, &["=="]),
            ok: lident(arena, "Ok"),
            error_constructor: lident(arena, "Error"),
            path: lident(arena, "path"),
            decode_error: lident_path_parse(arena, &["Spice", "decodeError"]),
        }
    }
}

/// The locals of a decoder: the two parameters, then `json_arr` (or
/// `str_or_num`).
const VALUE: u32 = 1;
const JSON_ARR: u32 = 2;
/// The first local a case of a constructor binds.
const CASE: u32 = 3;
/// The first local an encoder's case binds.
const ENCODED: u32 = 2;

/// What a decoder's bodies share.
struct Decoder<'a> {
    lids: &'a Lids,
    names: &'a Names,
    /// The `Type` obligation of the annotation `(v: JSON.t)`.
    json: ObligationIdx,
    /// The variable of the decoder's result.
    result: u32,
    /// The variable of the declared type.
    declared: u32,
    /// The variable of `json_arr`.
    arr: u32,
}

impl Builder<'_> {
    /// Cost: O(1), one pattern slot.
    fn pattern(&mut self, node: PatNode) -> PatIdx {
        self.arena.plans_mut().push_pattern(node)
    }

    /// `n` fresh variables, consecutive: the first. Cost: O(1).
    fn fresh_n(&mut self, n: u32) -> u32 {
        self.vars += n;
        self.vars - n
    }

    /// The skeletons `Var(first) ... Var(first + n - 1)`, then `Var(result)`:
    /// the first. Cost: O(n), one skeleton slot each.
    fn vars_then(&mut self, first: u32, n: u32, result: u32) -> SkeletonIdx {
        let start = self.arena.plans().next_skeleton();
        for i in 0..n {
            self.var(first + i);
        }
        self.var(result);
        start
    }

    /// The name of a declared constructor. Cost: O(1), one longident.
    fn declared_name(&mut self, constructor: &ConstructorDeclaration) -> LidentIdx {
        self.arena.push_lident_from_idx(constructor.pcd_name.txt)
    }

    /// `Spice.error` used with a value of variable `value`, or of `JSON.t`,
    /// and the decoder's result.
    /// Cost: O(1): one obligation, six skeleton slots and one body slot.
    fn spice_error(&mut self, decoder: &Decoder<'_>, value: Option<u32>) -> BodyIdx {
        let path = self.fresh();
        let skeleton = self.error_skeleton(path);
        self.string();
        match value {
            Some(var) => self.var(var),
            None => self.json(decoder.json),
        };
        self.var(decoder.result);
        self.value_named(decoder.lids.error, skeleton)
    }

    /// `Spice.error(message, v)`. Cost: O(1).
    fn error_of_value(&mut self, decoder: &Decoder<'_>, message: &str) -> BodyIdx {
        let error = self.spice_error(decoder, None);
        let message = self.arena.intern_string(message);
        let message = self.node(BodyNode::Str(message));
        let v = self.node(BodyNode::Local(VALUE));
        self.apply_error(error, &[message, v])
    }

    /// `Array.getUnsafe(json_arr, index)`, of variable `result`.
    /// Cost: O(1): one obligation, four skeleton and four body slots.
    fn get_unsafe(&mut self, decoder: &Decoder<'_>, index: i32, result: u32) -> BodyIdx {
        let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
        self.var(decoder.arr);
        self.sk(SkeletonNode::Predef {
            ty: Predef::Int,
            args: 0,
        });
        self.var(result);
        let get = self.value_named(decoder.lids.get_unsafe, skeleton);
        let arr = self.node(BodyNode::Local(JSON_ARR));
        let index = self.node(BodyNode::Int(index));
        self.apply(get, &[arr, index])
    }

    /// A `Switch` of the cases gathered in the case buffer from `first_case`
    /// on, which it takes. Cost: O(cases).
    fn switch(&mut self, scrutinee: BodyIdx, first_case: usize) -> BodyIdx {
        let len = (self.scratch.cases.len() - first_case) as u16;
        let plans = self.arena.plans_mut();
        let cases = plans.push_cases(&self.scratch.cases[first_case..]);
        self.scratch.cases.truncate(first_case);
        plans.push_body(BodyNode::Switch {
            scrutinee,
            cases,
            len,
        })
    }

    /// The encoder of a variant: the root of its body and its stated type.
    /// Cost: O(constructors + arguments + codecs of their types + fields of
    /// inline records): per constructor a fixed number of obligations,
    /// pattern and body nodes beside those of its arguments' codecs and
    /// inline record; the cases are gathered in the item's case buffer.
    fn variant_encoder(
        &mut self,
        constructors: &[ConstructorDeclaration],
        mode: Mode,
        names: &Names,
    ) -> (BodyIdx, SkeletonIdx) {
        let lids = Lids::of(self.arena);
        let json_name = self.arena.spice_json_ctyp_lident();
        let json = self.arena.plans_mut().push_obligation(Obligation::Type {
            name: json_name,
            name_loc: names.none,
            arity: 0,
            var: NO_VAR,
        });
        let declared = self.fresh();


        // The patterns of all cases.
        let (first_case, first_var) = (self.scratch.cases.len(), self.scratch.vars.len());
        for constructor in constructors {
            let name = self.declared_name(constructor);
            let pattern = match &constructor.pcd_args {
                ConstructorArguments::Pcstr_tuple(args) => {
                    let n = args.len() as u32;
                    let first = self.fresh_n(n);
                    self.scratch.vars.push(first);
                    let skeleton = self.vars_then(first, n, declared);
                    let constructor = self.constructor(
                        name,
                        Owner::Declared,
                        Site::Pattern,
                        n as u16,
                        skeleton,
                    );
                    let pattern = self.pattern(PatNode::Construct(constructor));
                    for i in 0..n {
                        let binder = self.indexed_name("v", i as usize, "");
                        self.pattern(PatNode::Var(binder));
                    }
                    pattern
                }
                ConstructorArguments::Pcstr_record(labels) => {
                    let record = self.fresh();
                    let skeleton = self.var(record);
                    self.var(declared);
                    let constructor = self.constructor(
                        name,
                        Owner::Declared,
                        Site::Pattern,
                        1,
                        skeleton,
                    );
                    let pattern = self.pattern(PatNode::Construct(constructor));
                    let first = self.fresh_n(labels.len() as u32);
                    self.scratch.vars.push(first);
                    let first_label = self.arena.plans().next_obligation();
                    self.pattern(PatNode::Record {
                        labels: first_label,
                        len: labels.len() as u16,
                    });
                    for (i, label) in labels.iter().enumerate() {
                        let name = self.arena.push_lident_from_idx(label.pld_name.txt);
                        self.label(name, LabelUse::Pattern, first + i as u32, record);
                        let binder = self.field_name(label.pld_name.txt);
                        self.pattern(PatNode::Var(binder));
                    }
                    pattern
                }
            };
            self.scratch.cases.push(Case {
                pattern: CasePattern::Nested(pattern),
                body: BodyIdx(0),
            });
        }

        // Their bodies.
        for (k, constructor) in constructors.iter().enumerate() {
            let body = match mode {
                Mode::Alias => {
                    let expr = alias(constructor, self.arena).expect("an aliased constructor");
                    let literal_var = self.fresh();
                    let skeleton = self.var(literal_var);
                    self.json(json);
                    let name = match alias_is_string(expr, self.arena) {
                        true => lids.json_string,
                        false => lids.json_number,
                    };
                    let wrap =
                        self.constructor(name, Owner::Type, Site::Construct, 1, skeleton);
                    let literal = self.literal(expr, Some(literal_var));
                    let arg = self.node(BodyNode::Literal(literal));
                    self.node(BodyNode::Construct {
                        constructor: wrap,
                        arg,
                    })
                }
                Mode::Array => {
                    let first = self.scratch.vars[first_var + k];
                    let element = self.fresh();
                    let skeleton = self.sk(SkeletonNode::Predef {
                        ty: Predef::Array,
                        args: 1,
                    });
                    self.var(element);
                    self.json(json);
                    let array = self.constructor(
                        lids.json_array,
                        Owner::Type,
                        Site::Construct,
                        1,
                        skeleton,
                    );
                    let skeleton = self.string();
                    self.var(element);
                    let string = self.constructor(
                        lids.json_string,
                        Owner::Type,
                        Site::Construct,
                        1,
                        skeleton,
                    );
                    let tag = self.node(BodyNode::Str(constructor.pcd_name.txt));
                    let head = self.node(BodyNode::Construct {
                        constructor: string,
                        arg: tag,
                    });
                    let first_item = self.scratch.nodes.len();
                    self.scratch.nodes.push(head);
                    match &constructor.pcd_args {
                        ConstructorArguments::Pcstr_tuple(args) => {
                            for (i, arg) in args.iter().enumerate() {
                                let spec = Spec::Type(*arg, EncodeContext::Value);
                                let codec =
                                    self.codec(spec, Slot::Applied(first + i as u32, element));
                                let local = self.node(BodyNode::Local(ENCODED + i as u32));
                                let encoded = self.apply(codec, &[local]);
                                self.scratch.nodes.push(encoded);
                            }
                        }
                        ConstructorArguments::Pcstr_record(labels) => {
                            let values = FieldValues::Locals {
                                first_local: ENCODED,
                                first_var: first,
                            };
                            let (object, _) = self.object_encoder(labels, names, values);
                            self.scratch.nodes.push(object);
                        }
                    }
                    let len = (self.scratch.nodes.len() - first_item) as u32;
                    let plans = self.arena.plans_mut();
                    let args = plans.push_args(&self.scratch.nodes[first_item..]);
                    self.scratch.nodes.truncate(first_item);
                    let elements = plans.push_body(BodyNode::Array { args, len });
                    self.node(BodyNode::Construct {
                        constructor: array,
                        arg: elements,
                    })
                }
            };
            self.scratch.cases[first_case + k].body = body;
        }
        self.scratch.vars.truncate(first_var);
        let scrutinee = self.node(BodyNode::Local(1));
        let body = self.switch(scrutinee, first_case);
        let param = self.arena.spice_pat_v();
        let root = self.eta(body, param);
        let stated = self.sk(SkeletonNode::Arrow { params: 1 });
        self.var(declared);
        self.json(json);
        (root, stated)
    }

    /// The decoder of a variant written as arrays: the root of its body and
    /// its stated type.
    /// Cost: O(constructors + arguments + codecs of their types + fields of
    /// inline records): per constructor a fixed number of obligations,
    /// pattern and body nodes beside those of its arguments' codecs and
    /// inline record.
    fn variant_decoder(
        &mut self,
        constructors: &[ConstructorDeclaration],
        names: &Names,
    ) -> (BodyIdx, SkeletonIdx) {
        let lids = Lids::of(self.arena);
        let json = self.decoder_json(names, NO_VAR);
        let (result, declared, empty, arr) =
            (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        let decoder = Decoder {
            lids: &lids,
            names,
            json,
            result,
            declared,
            arr,
        };
        let skeleton = self.var(empty);
        self.json(json);
        let empty_array = self.constructor(
            lids.json_array,
            Owner::Type,
            Site::PatternDummy,
            1,
            skeleton,
        );
        let empty_pattern = self.pattern(PatNode::Construct(empty_array));
        self.pattern(PatNode::EmptyArray);
        let skeleton = self.var(arr);
        self.json(json);
        let array = self.constructor(
            lids.json_array,
            Owner::Type,
            Site::PatternDummy,
            1,
            skeleton,
        );

        let empty = self.error_of_value(&decoder, "Expected variant, found empty array");
        let tagged = self.tag_switch(&decoder, constructors);
        let other = self.error_of_value(&decoder, "Not a variant");

        let scrutinee = self.node(BodyNode::Local(VALUE));
        let json_arr = self.arena.intern_string("json_arr");
        let plans = self.arena.plans_mut();
        let cases = plans.push_cases(&[
            Case {
                pattern: CasePattern::Nested(empty_pattern),
                body: empty,
            },
            Case {
                pattern: CasePattern::Construct {
                    constructor: array,
                    binder: json_arr,
                },
                body: tagged,
            },
            Case {
                pattern: CasePattern::Any,
                body: other,
            },
        ]);
        let body = plans.push_body(BodyNode::Switch {
            scrutinee,
            cases,
            len: 3,
        });
        let param = self.arena.spice_pat_v();
        let root = self.eta(body, param);
        let stated = self.sk(SkeletonNode::Arrow { params: 1 });
        self.json(json);
        self.var(result);
        (root, stated)
    }

    /// `switch Array.getUnsafe(json_arr, 0) { | JSON.String("C") => ... |
    /// _ => Spice.error("Invalid variant constructor", ...) }`.
    /// Cost: that of [`Builder::variant_decoder`].
    fn tag_switch(
        &mut self,
        decoder: &Decoder<'_>,
        constructors: &[ConstructorDeclaration],
    ) -> BodyIdx {
        let head = self.fresh();
        let scrutinee = self.get_unsafe(decoder, 0, head);
        let first_case = self.scratch.cases.len();
        for constructor in constructors {
            let skeleton = self.string();
            self.var(head);
            let string = self.constructor(
                decoder.lids.json_string,
                Owner::Type,
                Site::Pattern,
                1,
                skeleton,
            );
            let pattern = self.pattern(PatNode::Construct(string));
            self.pattern(PatNode::Str(constructor.pcd_name.txt));
            self.scratch.cases.push(Case {
                pattern: CasePattern::Nested(pattern),
                body: BodyIdx(0),
            });
        }
        self.scratch.cases.push(Case {
            pattern: CasePattern::Any,
            body: BodyIdx(0),
        });
        for (k, constructor) in constructors.iter().enumerate() {
            let body = self.tag_case(decoder, constructor);
            self.scratch.cases[first_case + k].body = body;
        }
        let other_head = self.fresh();
        let error = self.spice_error(decoder, Some(other_head));
        let message = self.arena.intern_string("Invalid variant constructor");
        let message = self.node(BodyNode::Str(message));
        let value = self.get_unsafe(decoder, 0, other_head);
        let other = self.apply_error(error, &[message, value]);
        self.scratch.cases[first_case + constructors.len()].body = other;
        self.switch(scrutinee, first_case)
    }

    /// The body of the case of one constructor: the argument-count test,
    /// then its decoding (`variants_generate_decoder_case`).
    /// Cost: O(arguments + codecs of their types + fields of an inline
    /// record).
    fn tag_case(&mut self, decoder: &Decoder<'_>, constructor: &ConstructorDeclaration) -> BodyIdx {
        let count = match &constructor.pcd_args {
            ConstructorArguments::Pcstr_tuple(args) => args.len(),
            ConstructorArguments::Pcstr_record(_) => 1,
        };
        let length = self.fresh();
        let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
        self.var(length);
        self.sk(SkeletonNode::Predef {
            ty: Predef::Int,
            args: 0,
        });
        self.sk(SkeletonNode::Predef {
            ty: Predef::Bool,
            args: 0,
        });
        let not_equal = self.value_named(decoder.lids.not_equal, skeleton);
        let skeleton = self.sk(SkeletonNode::Arrow { params: 1 });
        self.var(decoder.arr);
        self.var(length);
        let length = self.value_named(decoder.lids.length, skeleton);
        let arr = self.node(BodyNode::Local(JSON_ARR));
        let length = self.apply(length, &[arr]);
        let expected = self.node(BodyNode::Int(count as i32 + 1));
        let cond = self.apply(not_equal, &[length, expected]);
        let then = self.error_of_value(
            decoder,
            "Invalid number of arguments to variant constructor",
        );
        let else_ = match &constructor.pcd_args {
            ConstructorArguments::Pcstr_tuple(args) if args.is_empty() => {
                self.ok_of_constant(decoder, constructor)
            }
            ConstructorArguments::Pcstr_tuple(args) => self.arguments(decoder, constructor, args),
            ConstructorArguments::Pcstr_record(labels) => {
                self.inline_record(decoder, constructor, labels)
            }
        };
        self.node(BodyNode::If { cond, then, else_ })
    }

    /// `Ok(C)` of a constant constructor. Cost: O(1).
    fn ok_of_constant(
        &mut self,
        decoder: &Decoder<'_>,
        constructor: &ConstructorDeclaration,
    ) -> BodyIdx {

        let skeleton = self.var(decoder.declared);
        self.var(decoder.result);
        let ok = self.constructor(
            decoder.lids.ok,
            Owner::Result,
            Site::Construct,
            1,
            skeleton,
        );
        let name = self.declared_name(constructor);
        let skeleton = self.var(decoder.declared);
        let declared = self.constructor(
            name,
            Owner::Declared,
            Site::ConstructNone,
            0,
            skeleton,
        );
        let arg = self.node(BodyNode::Construct {
            constructor: declared,
            arg: BodyIdx(0),
        });
        self.node(BodyNode::Construct {
            constructor: ok,
            arg,
        })
    }

    /// `Error({...e, path: prefix ++ e.path})` of the local `e`, an error of
    /// variable `failure` (`generate_error_case`,
    /// `prefix_decode_error_path`).
    /// Cost: O(1): four obligations and eight body slots.
    fn prefixed_error(
        &mut self,
        decoder: &Decoder<'_>,
        failure: u32,
        prefix: StrIdx,
        e: u32,
    ) -> BodyIdx {

        let skeleton = self.var(failure);
        self.var(decoder.result);
        let error = self.constructor(
            decoder.lids.error_constructor,
            Owner::Result,
            Site::Construct,
            1,
            skeleton,
        );
        let (path, previous) = (self.fresh(), self.fresh());
        let base = self.node(BodyNode::Local(e));
        let label = self.label(decoder.lids.path, LabelUse::Update, path, failure);
        let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
        self.string();
        self.var(previous);
        self.var(path);
        let concat = self.value_named(decoder.lids.concat, skeleton);
        let prefix = self.node(BodyNode::Str(prefix));
        let record = self.node(BodyNode::Local(e));
        let access = self.label(decoder.lids.path, LabelUse::AccessDummy, previous, failure);
        let previous = self.node(BodyNode::Field {
            record,
            label: access,
        });
        let value = self.apply(concat, &[prefix, previous]);
        let updated = self.node(BodyNode::Update { base, label, value });
        self.node(BodyNode::Construct {
            constructor: error,
            arg: updated,
        })
    }

    /// The pattern `Error(e: Spice.decodeError)` of a scrutinee of variable
    /// `scrutinee`, its error of variable `failure`.
    /// Cost: O(1): two obligations and two pattern slots.
    fn error_pattern(&mut self, decoder: &Decoder<'_>, failure: u32, scrutinee: u32) -> PatIdx {
        let skeleton = self.var(failure);
        self.var(scrutinee);
        let error = self.constructor(
            decoder.lids.error_constructor,
            Owner::Result,
            Site::PatternDummy,
            1,
            skeleton,
        );
        let pattern = self.pattern(PatNode::Construct(error));
        self.arena.plans_mut().push_obligation(Obligation::Type {
            name: decoder.lids.decode_error,
            name_loc: decoder.names.dummy,
            arity: 0,
            var: failure,
        });
        let e = self.arena.intern_string("e");
        self.pattern(PatNode::Var(e));
        pattern
    }

    /// The decoding of a constructor's arguments
    /// (`variants_generate_arg_decoder`): a match on the decoded argument, or
    /// on the tuple of them.
    /// Cost: O(arguments + codecs of their types): per argument a fixed
    /// number of obligations, pattern and body nodes beside its codec's, and
    /// one pattern node per argument in each of the `n` error cases: O(n²)
    /// pattern nodes for `n` arguments, as the general form has; `n` is at
    /// most 255.
    fn arguments(
        &mut self,
        decoder: &Decoder<'_>,
        constructor: &ConstructorDeclaration,
        args: &[CoreTypeIdx],
    ) -> BodyIdx {
        let n = args.len() as u32;
        let results = self.fresh_n(n);
        let first_item = self.scratch.nodes.len();
        for (i, arg) in args.iter().enumerate() {
            let read = self.fresh();
            let spec = Spec::Type(*arg, EncodeContext::Value);
            let codec = self.codec(spec, Slot::Applied(read, results + i as u32));
            let value = self.get_unsafe(decoder, i as i32 + 1, read);
            let decoded = self.apply(codec, &[value]);
            self.scratch.nodes.push(decoded);
        }
        let scrutinee = if n == 1 {
            self.scratch.nodes[first_item]
        } else {
            let plans = self.arena.plans_mut();
            let items = plans.push_args(&self.scratch.nodes[first_item..]);
            plans.push_body(BodyNode::Tuple {
                args: items,
                len: n,
            })
        };
        self.scratch.nodes.truncate(first_item);

        // `(Ok(v0), Ok(v1), ...)`.

        let first_case = self.scratch.cases.len();
        let values = self.fresh_n(n);
        let tuple = (n > 1).then(|| self.pattern(PatNode::Tuple { len: n as u16 }));
        let mut success = None;
        for i in 0..n {
            let skeleton = self.var(values + i);
            self.var(results + i);
            let ok = self.constructor(
                decoder.lids.ok,
                Owner::Result,
                Site::PatternDummy,
                1,
                skeleton,
            );
            let pattern = self.pattern(PatNode::Construct(ok));
            success.get_or_insert(pattern);
            let binder = self.indexed_name("v", i as usize, "");
            self.pattern(PatNode::Var(binder));
        }
        let success = tuple.or(success).expect("a constructor with arguments");
        self.scratch.cases.push(Case {
            pattern: CasePattern::Nested(success),
            body: BodyIdx(0),
        });
        // `(Error(e: Spice.decodeError), _, ...)`, one per argument.
        let failures = self.fresh_n(n);
        for i in 0..n {
            let tuple = (n > 1).then(|| self.pattern(PatNode::Tuple { len: n as u16 }));
            let mut error = None;
            for j in 0..n {
                if j == i {
                    error = Some(self.error_pattern(decoder, failures + i, results + i));
                } else {
                    self.pattern(PatNode::Any);
                }
            }
            let pattern = tuple.or(error).expect("an error pattern");
            self.scratch.cases.push(Case {
                pattern: CasePattern::Nested(pattern),
                body: BodyIdx(0),
            });
        }

        // `Ok(C(v0, ...))`.
        let skeleton = self.var(decoder.declared);
        self.var(decoder.result);
        let ok = self.constructor(
            decoder.lids.ok,
            Owner::Result,
            Site::Construct,
            1,
            skeleton,
        );
        let name = self.declared_name(constructor);
        let skeleton = self.vars_then(values, n, decoder.declared);
        let declared = self.constructor(
            name,
            Owner::Declared,
            Site::ConstructNone,
            n as u16,
            skeleton,
        );
        let made = if n == 1 {
            let arg = self.node(BodyNode::Local(CASE));
            self.node(BodyNode::Construct {
                constructor: declared,
                arg,
            })
        } else {
            let first_value = self.scratch.nodes.len();
            for i in 0..n {
                let local = self.node(BodyNode::Local(CASE + i));
                self.scratch.nodes.push(local);
            }
            let plans = self.arena.plans_mut();
            let args = plans.push_args(&self.scratch.nodes[first_value..]);
            self.scratch.nodes.truncate(first_value);
            plans.push_body(BodyNode::ConstructArgs {
                constructor: declared,
                args,
            })
        };
        let body = self.node(BodyNode::Construct {
            constructor: ok,
            arg: made,
        });
        self.scratch.cases[first_case].body = body;
        for i in 0..n {
            let prefix = self.indexed_name("[", i as usize + 1, "]");
            let body = self.prefixed_error(decoder, failures + i, prefix, CASE);
            self.scratch.cases[first_case + 1 + i as usize].body = body;
        }
        self.switch(scrutinee, first_case)
    }

    /// The decoding of an inline record: its object decoder on the second
    /// element, whose errors are prefixed with `[1]`.
    /// Cost: that of [`Builder::object_decoder`] and a fixed number of
    /// nodes.
    fn inline_record(
        &mut self,
        decoder: &Decoder<'_>,
        constructor: &ConstructorDeclaration,
        labels: &[LabelDeclaration],
    ) -> BodyIdx {
        let read = self.fresh();
        let value = self.get_unsafe(decoder, 1, read);
        let json = self.decoder_json(decoder.names, read);
        let inner = self.fresh();
        let inline = Some((constructor.pcd_name.txt, decoder.declared));
        let decoded = self.object_decoder(labels, decoder.names, json, inner, CASE, inline);
        let param = self.arena.spice_pat_v();
        let scrutinee = self.node(BodyNode::Let {
            param,
            value,
            body: decoded,
        });

        let (made, failure) = (self.fresh(), self.fresh());
        let skeleton = self.var(made);
        self.var(inner);
        let ok_pattern = self.constructor(
            decoder.lids.ok,
            Owner::Result,
            Site::PatternDummy,
            1,
            skeleton,
        );
        let error_pattern = self.error_pattern(decoder, failure, inner);

        let skeleton = self.var(made);
        self.var(decoder.result);
        let ok = self.constructor(
            decoder.lids.ok,
            Owner::Result,
            Site::Construct,
            1,
            skeleton,
        );
        let local = self.node(BodyNode::Local(CASE));
        let success = self.node(BodyNode::Construct {
            constructor: ok,
            arg: local,
        });
        let prefix = self.arena.intern_string("[1]");
        let failed = self.prefixed_error(decoder, failure, prefix, CASE);
        let plans = self.arena.plans_mut();
        let cases = plans.push_cases(&[
            Case {
                pattern: CasePattern::Construct {
                    constructor: ok_pattern,
                    binder: param,
                },
                body: success,
            },
            Case {
                pattern: CasePattern::Nested(error_pattern),
                body: failed,
            },
        ]);
        plans.push_body(BodyNode::Switch {
            scrutinee,
            cases,
            len: 2,
        })
    }

    /// The decoder of a variant whose constructors are written as their
    /// `@spice.as` literals: the root of its body and its stated type.
    /// Cost: O(constructors): per constructor four obligations; the
    /// conditions are gathered in the item's node buffer.
    fn alias_decoder(
        &mut self,
        constructors: &[ConstructorDeclaration],
        names: &Names,
    ) -> (BodyIdx, SkeletonIdx) {
        let lids = Lids::of(self.arena);
        let json = self.decoder_json(names, NO_VAR);
        let (result, declared, string, number) =
            (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        let decoder = Decoder {
            lids: &lids,
            names,
            json,
            result,
            declared,
            arr: NO_VAR,
        };
        let skeleton = self.var(string);
        self.json(json);
        let string_pattern = self.constructor(
            lids.json_string,
            Owner::Type,
            Site::PatternDummy,
            1,
            skeleton,
        );
        let skeleton = self.var(number);
        self.json(json);
        let number_pattern = self.constructor(
            lids.json_number,
            Owner::Type,
            Site::PatternDummy,
            1,
            skeleton,
        );
        let strings = self.literal_chain(&decoder, constructors, true, string);
        let numbers = self.literal_chain(&decoder, constructors, false, number);
        let other = self.error_of_value(&decoder, "Not a JSONString");

        let scrutinee = self.node(BodyNode::Local(VALUE));
        let binder = self.arena.intern_string("str_or_num");
        let plans = self.arena.plans_mut();
        let cases = plans.push_cases(&[
            Case {
                pattern: CasePattern::Construct {
                    constructor: string_pattern,
                    binder,
                },
                body: strings,
            },
            Case {
                pattern: CasePattern::Construct {
                    constructor: number_pattern,
                    binder,
                },
                body: numbers,
            },
            Case {
                pattern: CasePattern::Any,
                body: other,
            },
        ]);
        let body = plans.push_body(BodyNode::Switch {
            scrutinee,
            cases,
            len: 3,
        });
        let param = self.arena.spice_pat_v();
        let root = self.eta(body, param);
        let stated = self.sk(SkeletonNode::Arrow { params: 1 });
        self.json(json);
        self.var(result);
        (root, stated)
    }

    /// `if lit1 == str_or_num { Ok(C1) } else if ... else {
    /// Spice.error("Not matched", v) }` over the constructors whose literal
    /// is a string (`strings`) or a number, compared with the local
    /// `str_or_num` of variable `value` (`build_ifthenelse_with_prefix`).
    /// Cost: O(constructors); the conditions and values are gathered in the
    /// item's node buffer.
    fn literal_chain(
        &mut self,
        decoder: &Decoder<'_>,
        constructors: &[ConstructorDeclaration],
        strings: bool,
        value: u32,
    ) -> BodyIdx {
        let first = self.scratch.nodes.len();
        for constructor in constructors {
            let expr = alias(constructor, self.arena).expect("an aliased constructor");
            if alias_is_string(expr, self.arena) != strings {
                continue;
            }
            let literal_var = self.fresh();
            let skeleton = self.sk(SkeletonNode::Arrow { params: 2 });
            self.var(literal_var);
            self.var(value);
            self.sk(SkeletonNode::Predef {
                ty: Predef::Bool,
                args: 0,
            });
            // `expr_equal`: the name has no location.
            let name_loc = decoder.names.none;
            let plans = self.arena.plans_mut();
            let equal = plans.push_obligation(Obligation::Value {
                name: decoder.lids.equal,
                name_loc,
                skeleton,
                expr_loc: ExprLoc::Dummy,
                called: true,
            });
            let equal = plans.push_body(BodyNode::Free(equal));
            let literal = self.literal(expr, Some(literal_var));
            let literal = self.node(BodyNode::Literal(literal));
            let local = self.node(BodyNode::Local(JSON_ARR));
            let cond = self.apply(equal, &[literal, local]);
            let then = self.ok_of_constant(decoder, constructor);
            self.scratch.nodes.push(cond);
            self.scratch.nodes.push(then);
        }
        let mut body = self.error_of_value(decoder, "Not matched");
        while self.scratch.nodes.len() > first {
            let then = self.scratch.nodes.pop().expect("a value");
            let cond = self.scratch.nodes.pop().expect("a condition");
            body = self.node(BodyNode::If {
                cond,
                then,
                else_: body,
            });
        }
        body
    }
}

/// Append the bindings of a variant declaration that [`planned`] admits:
/// `<type>_encode`, `<type>_encodeJson` (the same encoder) and
/// `<type>_decode`.
/// Cost: O(constructors + arguments + codecs of their types + fields of
/// inline records) per binding.
pub(super) fn bindings(
    arena: &mut ParseArena,
    type_name: &str,
    constructors: &[ConstructorDeclaration],
    settings: GeneratorSettings,
    scratch: &mut Scratch,
) {
    let names = Names::of(arena);
    let mode = match constructors.iter().any(|c| alias(c, arena).is_some()) {
        true => Mode::Alias,
        false => Mode::Array,
    };
    record::stated_bindings(arena, type_name, settings, scratch, |builder| {
        match (builder.side, mode) {
            (Side::Encode, mode) => builder.variant_encoder(constructors, mode, &names),
            (Side::Decode, Mode::Array) => builder.variant_decoder(constructors, &names),
            (Side::Decode, Mode::Alias) => builder.alias_decoder(constructors, &names),
        }
    });
}

#[cfg(test)]
mod layout_tests {
    use super::*;

    #[test]
    fn variant_builder_state_sizes_are_pinned() {
        assert_eq!(std::mem::size_of::<Mode>(), 1);
        assert_eq!(std::mem::size_of::<Lids>(), 52);
        assert_eq!(std::mem::size_of::<Decoder<'_>>(), 32);
        assert_eq!(std::mem::size_of::<&Decoder<'_>>(), 8);
    }
}
