//! H12: K:60 compile_constant, K:34 compile_some_constant, K:26 nested_some_none.
use super::State;
use crate::bir::{Cold, ConstId, Constant, JsPayload, NodeId, View};
use crate::lambda::LamLoc;
use crate::lambda::lam_constant::{ConstructorRuntimeTag, PointerInfo};
use crate::types::VariantLiteralTag;

pub(super) enum Work {
    Enter(ConstId),
    Block(crate::lambda::lam_tag_info::TagInfo, usize),
    Some,
}
impl State {
    /// H12: K:48 compile_runtime_int. Large constructor integers print as floats.
    fn runtime_int(&mut self, n: i64) -> NodeId {
        if i32::try_from(n).is_ok() {
            self.number(Constant::Int(n))
        } else {
            self.float(&n.to_string())
        }
    }
    /// H12: K:60 compile_constant, numeric leaf with preserved spelling.
    fn number(&mut self, value: Constant) -> NodeId {
        let value = self.arena.intern_const(value);
        self.pure_expression(View::JNumber { value }, 0)
    }
    /// H12: K:60 compile_constant, float payload has already been validated by import.
    fn float(&mut self, spelling: &str) -> NodeId {
        let value = self
            .arena
            .intern_float(spelling)
            .expect("valid imported float");
        self.pure_expression(View::JNumber { value }, 0)
    }
    /// H12: K:60 compile_constant, decoded string bytes are not re-escaped here.
    fn string(&mut self, text: &str) -> NodeId {
        let text = self.arena.intern_text(text);
        self.pure_expression(View::JStr { text }, 0)
    }
    /// N7: K:55 commented_number; decoration remains until the printer migration.
    fn comment(&mut self, node: NodeId, text: &str) -> NodeId {
        let comment = Some(self.arena.intern_text(text));
        self.arena.set_cold(
            node,
            Cold {
                loc: LamLoc::NONE,
                comment,
            },
        );
        node
    }
    /// H12: K:60 compile_constant. An explicit stack also handles deeply nested
    /// constant blocks and options; each constant occurrence is visited once.
    pub(super) fn constant(&mut self, root: ConstId) -> NodeId {
        let mut work = std::mem::take(&mut self.constant_work);
        let mut values = std::mem::take(&mut self.constant_values);
        work.push(Work::Enter(root));
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(id) => {
                    let constant = self.arena.constant(id).clone();
                    let mut none = false;
                    let value = match constant {
                        Constant::Block { tag, fields } => {
                            let fields = self.arena.constant_fields(fields);
                            work.push(Work::Block(tag, fields.len()));
                            work.extend(fields.iter().rev().copied().map(Work::Enter));
                            continue;
                        }
                        Constant::Some(inner) => {
                            work.push(Work::Some);
                            work.push(Work::Enter(inner));
                            continue;
                        }
                        Constant::Null => self.pure_expression(View::JNull, 0),
                        Constant::Undefined(unit) => {
                            none = true;
                            self.pure_expression(View::JUndefined, u16::from(unit))
                        }
                        Constant::ModuleAlias => {
                            none = true;
                            self.pure_expression(View::JUndefined, 0)
                        }
                        Constant::Bool(b) => self.pure_expression(View::JBool, u16::from(b)),
                        Constant::Int(n) => self.number(Constant::Int(n)),
                        Constant::NativeInt(n) => self.float(&n.to_string()),
                        Constant::Char(n) => self.number(Constant::Char(n)),
                        Constant::Float(_) | Constant::BigInt(_) => {
                            self.pure_expression(View::JNumber { value: id }, 0)
                        }
                        Constant::String(text)
                        | Constant::ImmString(text)
                        | Constant::Pointer(text) => self.pure_expression(View::JStr { text }, 0),
                        Constant::Constructor(tag) => {
                            if tag.name == "[]" {
                                let value = self.number(Constant::Int(0));
                                self.comment(value, &tag.name)
                            } else {
                                match tag.literal {
                                    VariantLiteralTag::Int(n) => {
                                        self.number(Constant::Int(i64::from(n as i32)))
                                    }
                                    VariantLiteralTag::String(s) => self.string(&s),
                                    VariantLiteralTag::Float(s) => self.float(&s),
                                    VariantLiteralTag::BigInt(s) => {
                                        let (positive, digits) =
                                            crate::types::typecore::parse_bigint_literal(&s);
                                        let text = self.arena.intern_text(&format!(
                                            "{}{digits}",
                                            if positive { "+" } else { "-" }
                                        ));
                                        self.number(Constant::BigInt(text))
                                    }
                                    VariantLiteralTag::Bool(b) => {
                                        self.pure_expression(View::JBool, u16::from(b))
                                    }
                                    VariantLiteralTag::Null => self.pure_expression(View::JNull, 0),
                                    VariantLiteralTag::Undefined => {
                                        none = true;
                                        self.pure_expression(View::JUndefined, 0)
                                    }
                                }
                            }
                        }
                        Constant::DecoratedInt {
                            value,
                            native,
                            comment,
                        } => {
                            if let PointerInfo::Constructor(tag) = &comment {
                                if !native {
                                    let node = match &tag.runtime_tag {
                                        Some(ConstructorRuntimeTag::Int(n)) => self.runtime_int(*n),
                                        Some(ConstructorRuntimeTag::String(s)) => self.string(s),
                                        Some(ConstructorRuntimeTag::Float(s)) => self.float(s),
                                        Some(ConstructorRuntimeTag::BigInt(s)) => {
                                            let text = self.arena.intern_text(&format!("+{s}"));
                                            self.number(Constant::BigInt(text))
                                        }
                                        Some(ConstructorRuntimeTag::Bool(b)) => {
                                            self.pure_expression(View::JBool, u16::from(*b))
                                        }
                                        Some(ConstructorRuntimeTag::Null) => {
                                            self.pure_expression(View::JNull, 0)
                                        }
                                        Some(ConstructorRuntimeTag::Undefined) => {
                                            self.pure_expression(View::JUndefined, 0)
                                        }
                                        None if tag.name != "[]" => self.string(&tag.name),
                                        None => {
                                            let node = self.number(Constant::Int(value));
                                            self.comment(node, &tag.name)
                                        }
                                    };
                                    values.push((node, false));
                                    continue;
                                }
                            }
                            let node = if native {
                                self.float(&value.to_string())
                            } else {
                                self.number(Constant::Int(value))
                            };
                            match comment {
                                PointerInfo::None | PointerInfo::ShapeNone => node,
                                PointerInfo::Constructor(tag) => self.comment(node, &tag.name),
                                PointerInfo::AssertFalse => self.comment(node, "assert_false"),
                                PointerInfo::Some(s) | PointerInfo::PolyVariant(s) => {
                                    self.comment(node, &s)
                                }
                            }
                        }
                    };
                    values.push((value, none));
                }
                Work::Block(tag, count) => {
                    let start = values.len() - count;
                    let children: Vec<_> = values.drain(start..).map(|(node, _)| node).collect();
                    let info = self.arena.js_info(JsPayload::Block(tag));
                    let node = self.pure_expression(
                        View::JBlockLit {
                            values: &children,
                            info,
                        },
                        2,
                    );
                    values.push((node, false));
                }
                Work::Some => {
                    let (mut value, none) = values.pop().expect("constant option child");
                    if none && self.arena.node(value).op() == crate::bir::Op::JUndefined {
                        self.arena.release(value);
                        value = self.pure_expression(View::JUndefined, 0);
                    }
                    let node = self.pure_expression(View::JOptional { value }, u16::from(!none));
                    values.push((node, none));
                }
            }
        }
        assert_eq!(values.len(), 1);
        let result = values.pop().expect("constant result").0;
        self.constant_work = work;
        self.constant_values = values;
        result
    }
}
