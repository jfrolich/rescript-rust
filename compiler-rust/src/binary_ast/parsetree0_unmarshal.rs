//! Reading the frozen Parsetree0 back from an OCaml marshaled value.
//!
//! An external `-ppx` rewriter returns its result in the binary protocol of
//! `compiler/core/cmd_ppx_apply.ml`: the magic string, the marshaled input
//! name, then the marshaled `Parsetree0.structure` / `signature`. This module
//! decodes the generic [`OcamlValue`] tree into [`parsetree0`] values; it is
//! the inverse of `parsetree0_marshal.rs` and follows the constructor order of
//! `compiler/ml/parsetree0.ml`.

use crate::cmi::marshal_reader::OcamlValue;
use crate::location::{Located, Location, Position};
use crate::parse_arena::ParseArena;
use crate::parser::longident::Longident;

use super::parsetree0::*;

/// A value that does not have the shape of the Parsetree0 type being read.
#[derive(Debug, Clone)]
pub struct DecodeError(pub String);

type R<T> = Result<T, DecodeError>;

fn err<T>(what: &str, v: &OcamlValue) -> R<T> {
    Err(DecodeError(format!(
        "expected {what}, found {}",
        v.short_debug()
    )))
}

/// Checked field access for decoded blocks.
///
/// A third-party PPX can return a block with fewer fields than the Parsetree0
/// constructor has; report that as a [`DecodeError`] instead of panicking.
trait FieldsExt {
    fn at(&self, i: usize) -> R<&OcamlValue>;
}

impl FieldsExt for [OcamlValue] {
    fn at(&self, i: usize) -> R<&OcamlValue> {
        self.get(i).ok_or_else(|| {
            DecodeError(format!(
                "expected a block with at least {} fields, found {}",
                i + 1,
                self.len()
            ))
        })
    }
}

/// The contents of an OCaml string value, borrowed (for strings that are only
/// interned).
fn str_ref(v: &OcamlValue) -> R<&str> {
    match v {
        OcamlValue::String(s) => Ok(s.as_str()),
        _ => err("string", v),
    }
}

/// Decodes Parsetree0 values, interning strings in the parse arena so that
/// equal strings share one index (as the Rust parser does).
pub struct Decoder<'a> {
    arena: &'a mut ParseArena,
}

impl<'a> Decoder<'a> {
    pub fn new(arena: &'a mut ParseArena) -> Self {
        Self { arena }
    }

    // ========== OCaml runtime representation ==========

    fn block<'v>(&self, v: &'v OcamlValue, what: &str) -> R<(u8, &'v [OcamlValue])> {
        match v.as_block_opt() {
            Some(b) => Ok(b),
            None => err(what, v),
        }
    }

    /// A record or tuple: block tag 0 with [n] fields.
    fn fields<'v>(&self, v: &'v OcamlValue, n: usize, what: &str) -> R<&'v [OcamlValue]> {
        match v.as_block_opt() {
            Some((0, fields)) if fields.len() == n => Ok(fields),
            _ => err(what, v),
        }
    }

    fn int(&self, v: &OcamlValue) -> R<i64> {
        match v {
            OcamlValue::Int(i) => Ok(*i),
            _ => err("int", v),
        }
    }

    fn bool(&self, v: &OcamlValue) -> R<bool> {
        Ok(self.int(v)? != 0)
    }

    fn string(&self, v: &OcamlValue) -> R<String> {
        match v {
            OcamlValue::String(s) => Ok(s.clone()),
            _ => err("string", v),
        }
    }

    fn list<T>(
        &mut self,
        v: &OcamlValue,
        mut f: impl FnMut(&mut Self, &OcamlValue) -> R<T>,
    ) -> R<Vec<T>> {
        let mut out = Vec::new();
        let mut cur = v;
        loop {
            match cur {
                OcamlValue::Int(0) => return Ok(out),
                OcamlValue::Block(0, cell) if cell.len() == 2 => {
                    out.push(f(self, &cell[0])?);
                    cur = &cell[1];
                }
                _ => return err("list", cur),
            }
        }
    }

    fn option<T>(
        &mut self,
        v: &OcamlValue,
        f: impl FnOnce(&mut Self, &OcamlValue) -> R<T>,
    ) -> R<Option<T>> {
        match v {
            OcamlValue::Int(0) => Ok(None),
            OcamlValue::Block(0, fields) if fields.len() == 1 => Ok(Some(f(self, &fields[0])?)),
            _ => err("option", v),
        }
    }

    fn char_option(&mut self, v: &OcamlValue) -> R<Option<char>> {
        self.option(v, |d, c| {
            let code = d.int(c)?;
            Ok(char::from_u32(code as u32).unwrap_or('\u{0}'))
        })
    }

    // ========== Locations and identifiers ==========

    fn position(&mut self, v: &OcamlValue) -> R<Position> {
        let f = self.fields(v, 4, "position")?;
        let fname = str_ref(f.at(0)?)?;
        Ok(Position {
            file_name: self.arena.intern(fname),
            line: self.int(f.at(1)?)? as i32,
            bol: self.int(f.at(2)?)? as i32,
            cnum: self.int(f.at(3)?)? as i32,
        })
    }

    fn location(&mut self, v: &OcamlValue) -> R<Location> {
        let f = self.fields(v, 3, "location")?;
        Ok(Location {
            loc_start: self.position(f.at(0)?)?,
            loc_end: self.position(f.at(1)?)?,
            loc_ghost: self.bool(f.at(2)?)?,
        })
    }

    fn located<T>(
        &mut self,
        v: &OcamlValue,
        f: impl FnOnce(&mut Self, &OcamlValue) -> R<T>,
    ) -> R<Located<T>> {
        let fields = self.fields(v, 2, "loc")?;
        let txt = f(self, &fields[0])?;
        let loc = self.location(&fields[1])?;
        Ok(Located { txt, loc })
    }

    fn string_loc(&mut self, v: &OcamlValue) -> R<Located<String>> {
        self.located(v, |d, s| d.string(s))
    }

    fn longident(&mut self, v: &OcamlValue) -> R<Longident> {
        let (tag, f) = self.block(v, "longident")?;
        Ok(match (tag, f.len()) {
            (0, 1) => Longident::Lident(self.arena.intern(str_ref(f.at(0)?)?)),
            (1, 2) => {
                let prefix = self.longident(f.at(0)?)?;
                Longident::Ldot(Box::new(prefix), self.arena.intern(str_ref(f.at(1)?)?))
            }
            (2, 2) => Longident::Lapply(
                Box::new(self.longident(f.at(0)?)?),
                Box::new(self.longident(f.at(1)?)?),
            ),
            _ => return err("longident", v),
        })
    }

    fn longident_loc(&mut self, v: &OcamlValue) -> R<Located<Longident>> {
        self.located(v, |d, l| d.longident(l))
    }

    // ========== Asttypes ==========

    fn rec_flag(&self, v: &OcamlValue) -> R<RecFlag> {
        Ok(if self.int(v)? == 0 {
            RecFlag::Nonrecursive
        } else {
            RecFlag::Recursive
        })
    }

    fn direction_flag(&self, v: &OcamlValue) -> R<DirectionFlag> {
        Ok(if self.int(v)? == 0 {
            DirectionFlag::Upto
        } else {
            DirectionFlag::Downto
        })
    }

    fn private_flag(&self, v: &OcamlValue) -> R<PrivateFlag> {
        Ok(if self.int(v)? == 0 {
            PrivateFlag::Private
        } else {
            PrivateFlag::Public
        })
    }

    fn mutable_flag(&self, v: &OcamlValue) -> R<MutableFlag> {
        Ok(if self.int(v)? == 0 {
            MutableFlag::Immutable
        } else {
            MutableFlag::Mutable
        })
    }

    fn override_flag(&self, v: &OcamlValue) -> R<OverrideFlag> {
        Ok(if self.int(v)? == 0 {
            OverrideFlag::Override
        } else {
            OverrideFlag::Fresh
        })
    }

    fn closed_flag(&self, v: &OcamlValue) -> R<ClosedFlag> {
        Ok(if self.int(v)? == 0 {
            ClosedFlag::Closed
        } else {
            ClosedFlag::Open
        })
    }

    fn variance(&self, v: &OcamlValue) -> R<Variance> {
        Ok(match self.int(v)? {
            0 => Variance::Covariant,
            1 => Variance::Contravariant,
            _ => Variance::Invariant,
        })
    }

    fn arg_label(&mut self, v: &OcamlValue) -> R<ArgLabel> {
        match v {
            OcamlValue::Int(0) => Ok(ArgLabel::Nolabel),
            OcamlValue::Block(0, f) if f.len() == 1 => {
                Ok(ArgLabel::Labelled(self.arena.intern(str_ref(f.at(0)?)?)))
            }
            OcamlValue::Block(1, f) if f.len() == 1 => {
                Ok(ArgLabel::Optional(self.arena.intern(str_ref(f.at(0)?)?)))
            }
            _ => err("arg_label", v),
        }
    }

    fn constant(&mut self, v: &OcamlValue) -> R<Constant> {
        let (tag, f) = self.block(v, "constant")?;
        Ok(match tag {
            0 => Constant::Integer(self.string(f.at(0)?)?, self.char_option(f.at(1)?)?),
            1 => Constant::Char(self.int(f.at(0)?)? as i32),
            2 => Constant::String(
                self.string(f.at(0)?)?,
                self.option(f.at(1)?, |d, s| d.string(s))?,
            ),
            3 => Constant::Float(self.string(f.at(0)?)?, self.char_option(f.at(1)?)?),
            _ => return err("constant", v),
        })
    }

    // ========== Attributes ==========

    fn attribute(&mut self, v: &OcamlValue) -> R<Attribute> {
        let f = self.fields(v, 2, "attribute")?;
        Ok((self.string_loc(f.at(0)?)?, self.payload(f.at(1)?)?))
    }

    fn attributes(&mut self, v: &OcamlValue) -> R<Attributes> {
        self.list(v, |d, a| d.attribute(a))
    }

    fn payload(&mut self, v: &OcamlValue) -> R<Payload> {
        let (tag, f) = self.block(v, "payload")?;
        Ok(match tag {
            0 => Payload::PStr(self.structure(f.at(0)?)?),
            1 => Payload::PSig(self.signature(f.at(0)?)?),
            2 => Payload::PTyp(Box::new(self.core_type(f.at(0)?)?)),
            3 => Payload::PPat(
                Box::new(self.pattern(f.at(0)?)?),
                self.option(f.at(1)?, |d, e| d.expression(e))?.map(Box::new),
            ),
            _ => return err("payload", v),
        })
    }

    // ========== Core types ==========

    fn core_type(&mut self, v: &OcamlValue) -> R<CoreType> {
        let f = self.fields(v, 3, "core_type")?;
        Ok(CoreType {
            ptyp_desc: self.core_type_desc(f.at(0)?)?,
            ptyp_loc: self.location(f.at(1)?)?,
            ptyp_attributes: self.attributes(f.at(2)?)?,
        })
    }

    fn core_type_desc(&mut self, v: &OcamlValue) -> R<CoreTypeDesc> {
        if let OcamlValue::Int(0) = v {
            return Ok(CoreTypeDesc::Any);
        }
        let (tag, f) = self.block(v, "core_type_desc")?;
        Ok(match tag {
            0 => CoreTypeDesc::Var(self.string(f.at(0)?)?),
            1 => CoreTypeDesc::Arrow(
                self.arg_label(f.at(0)?)?,
                Box::new(self.core_type(f.at(1)?)?),
                Box::new(self.core_type(f.at(2)?)?),
            ),
            2 => CoreTypeDesc::Tuple(self.list(f.at(0)?, |d, t| d.core_type(t))?),
            3 => CoreTypeDesc::Constr(
                self.longident_loc(f.at(0)?)?,
                self.list(f.at(1)?, |d, t| d.core_type(t))?,
            ),
            4 => CoreTypeDesc::Object(
                self.list(f.at(0)?, |d, o| d.object_field(o))?,
                self.closed_flag(f.at(1)?)?,
            ),
            5 => CoreTypeDesc::Class,
            6 => CoreTypeDesc::Alias(Box::new(self.core_type(f.at(0)?)?), self.string(f.at(1)?)?),
            7 => CoreTypeDesc::Variant(
                self.list(f.at(0)?, |d, r| d.row_field(r))?,
                self.closed_flag(f.at(1)?)?,
                self.option(f.at(2)?, |d, l| d.list(l, |d, s| d.string(s)))?,
            ),
            8 => CoreTypeDesc::Poly(
                self.list(f.at(0)?, |d, s| d.string_loc(s))?,
                Box::new(self.core_type(f.at(1)?)?),
            ),
            9 => CoreTypeDesc::Package(self.package_type(f.at(0)?)?),
            10 => CoreTypeDesc::Extension(self.attribute(f.at(0)?)?),
            _ => return err("core_type_desc", v),
        })
    }

    fn package_type(&mut self, v: &OcamlValue) -> R<PackageType> {
        let f = self.fields(v, 2, "package_type")?;
        let lid = self.longident_loc(f.at(0)?)?;
        let constraints = self.list(f.at(1)?, |d, c| {
            let f = d.fields(c, 2, "package constraint")?;
            Ok((d.longident_loc(f.at(0)?)?, d.core_type(f.at(1)?)?))
        })?;
        Ok((lid, constraints))
    }

    fn row_field(&mut self, v: &OcamlValue) -> R<RowField> {
        let (tag, f) = self.block(v, "row_field")?;
        Ok(match tag {
            0 => RowField::Rtag(
                self.string_loc(f.at(0)?)?,
                self.attributes(f.at(1)?)?,
                self.bool(f.at(2)?)?,
                self.list(f.at(3)?, |d, t| d.core_type(t))?,
            ),
            1 => RowField::Rinherit(self.core_type(f.at(0)?)?),
            _ => return err("row_field", v),
        })
    }

    fn object_field(&mut self, v: &OcamlValue) -> R<ObjectField> {
        let (tag, f) = self.block(v, "object_field")?;
        Ok(match tag {
            0 => ObjectField::Otag(
                self.string_loc(f.at(0)?)?,
                self.attributes(f.at(1)?)?,
                self.core_type(f.at(2)?)?,
            ),
            1 => ObjectField::Oinherit(self.core_type(f.at(0)?)?),
            _ => return err("object_field", v),
        })
    }

    // ========== Patterns ==========

    fn pattern(&mut self, v: &OcamlValue) -> R<Pattern> {
        let f = self.fields(v, 3, "pattern")?;
        Ok(Pattern {
            ppat_desc: self.pattern_desc(f.at(0)?)?,
            ppat_loc: self.location(f.at(1)?)?,
            ppat_attributes: self.attributes(f.at(2)?)?,
        })
    }

    fn opt_pattern(&mut self, v: &OcamlValue) -> R<Option<Box<Pattern>>> {
        Ok(self.option(v, |d, p| d.pattern(p))?.map(Box::new))
    }

    fn pattern_desc(&mut self, v: &OcamlValue) -> R<PatternDesc> {
        if let OcamlValue::Int(0) = v {
            return Ok(PatternDesc::Any);
        }
        let (tag, f) = self.block(v, "pattern_desc")?;
        Ok(match tag {
            0 => PatternDesc::Var(self.string_loc(f.at(0)?)?),
            1 => PatternDesc::Alias(
                Box::new(self.pattern(f.at(0)?)?),
                self.string_loc(f.at(1)?)?,
            ),
            2 => PatternDesc::Constant(self.constant(f.at(0)?)?),
            3 => PatternDesc::Interval(self.constant(f.at(0)?)?, self.constant(f.at(1)?)?),
            4 => PatternDesc::Tuple(self.list(f.at(0)?, |d, p| d.pattern(p))?),
            5 => PatternDesc::Construct(self.longident_loc(f.at(0)?)?, self.opt_pattern(f.at(1)?)?),
            6 => PatternDesc::Variant(self.string(f.at(0)?)?, self.opt_pattern(f.at(1)?)?),
            7 => PatternDesc::Record(
                self.list(f.at(0)?, |d, row| {
                    let f = d.fields(row, 2, "record pattern row")?;
                    Ok((d.longident_loc(f.at(0)?)?, d.pattern(f.at(1)?)?))
                })?,
                self.closed_flag(f.at(1)?)?,
            ),
            8 => PatternDesc::Array(self.list(f.at(0)?, |d, p| d.pattern(p))?),
            9 => PatternDesc::Or(
                Box::new(self.pattern(f.at(0)?)?),
                Box::new(self.pattern(f.at(1)?)?),
            ),
            10 => PatternDesc::Constraint(
                Box::new(self.pattern(f.at(0)?)?),
                Box::new(self.core_type(f.at(1)?)?),
            ),
            11 => PatternDesc::Type(self.longident_loc(f.at(0)?)?),
            12 => PatternDesc::Lazy(Box::new(self.pattern(f.at(0)?)?)),
            13 => PatternDesc::Unpack(self.string_loc(f.at(0)?)?),
            14 => PatternDesc::Exception(Box::new(self.pattern(f.at(0)?)?)),
            15 => PatternDesc::Extension(self.attribute(f.at(0)?)?),
            16 => PatternDesc::Open(
                self.longident_loc(f.at(0)?)?,
                Box::new(self.pattern(f.at(1)?)?),
            ),
            _ => return err("pattern_desc", v),
        })
    }

    // ========== Expressions ==========

    fn expression(&mut self, v: &OcamlValue) -> R<Expression> {
        let f = self.fields(v, 3, "expression")?;
        Ok(Expression {
            pexp_desc: self.expression_desc(f.at(0)?)?,
            pexp_loc: self.location(f.at(1)?)?,
            pexp_attributes: self.attributes(f.at(2)?)?,
        })
    }

    fn boxed(&mut self, v: &OcamlValue) -> R<Box<Expression>> {
        Ok(Box::new(self.expression(v)?))
    }

    fn opt_expression(&mut self, v: &OcamlValue) -> R<Option<Box<Expression>>> {
        Ok(self.option(v, |d, e| d.expression(e))?.map(Box::new))
    }

    fn cases(&mut self, v: &OcamlValue) -> R<Vec<Case>> {
        self.list(v, |d, c| {
            let f = d.fields(c, 3, "case")?;
            Ok(Case {
                pc_lhs: d.pattern(f.at(0)?)?,
                pc_guard: d.option(f.at(1)?, |d, g| d.expression(g))?,
                pc_rhs: d.expression(f.at(2)?)?,
            })
        })
    }

    fn expression_desc(&mut self, v: &OcamlValue) -> R<ExpressionDesc> {
        if let OcamlValue::Int(0) = v {
            return Ok(ExpressionDesc::Unreachable);
        }
        let (tag, f) = self.block(v, "expression_desc")?;
        Ok(match tag {
            0 => ExpressionDesc::Ident(self.longident_loc(f.at(0)?)?),
            1 => ExpressionDesc::Constant(self.constant(f.at(0)?)?),
            2 => ExpressionDesc::Let(
                self.rec_flag(f.at(0)?)?,
                self.list(f.at(1)?, |d, vb| d.value_binding(vb))?,
                self.boxed(f.at(2)?)?,
            ),
            3 => ExpressionDesc::Function(self.cases(f.at(0)?)?),
            4 => ExpressionDesc::Fun(
                self.arg_label(f.at(0)?)?,
                self.opt_expression(f.at(1)?)?,
                Box::new(self.pattern(f.at(2)?)?),
                self.boxed(f.at(3)?)?,
            ),
            5 => ExpressionDesc::Apply(
                self.boxed(f.at(0)?)?,
                self.list(f.at(1)?, |d, a| {
                    let f = d.fields(a, 2, "argument")?;
                    Ok((d.arg_label(f.at(0)?)?, d.expression(f.at(1)?)?))
                })?,
            ),
            6 => ExpressionDesc::Match(self.boxed(f.at(0)?)?, self.cases(f.at(1)?)?),
            7 => ExpressionDesc::Try(self.boxed(f.at(0)?)?, self.cases(f.at(1)?)?),
            8 => ExpressionDesc::Tuple(self.list(f.at(0)?, |d, e| d.expression(e))?),
            9 => ExpressionDesc::Construct(
                self.longident_loc(f.at(0)?)?,
                self.opt_expression(f.at(1)?)?,
            ),
            10 => ExpressionDesc::Variant(self.string(f.at(0)?)?, self.opt_expression(f.at(1)?)?),
            11 => ExpressionDesc::Record(
                self.list(f.at(0)?, |d, row| {
                    let f = d.fields(row, 2, "record row")?;
                    Ok((d.longident_loc(f.at(0)?)?, d.expression(f.at(1)?)?))
                })?,
                self.opt_expression(f.at(1)?)?,
            ),
            12 => ExpressionDesc::Field(self.boxed(f.at(0)?)?, self.longident_loc(f.at(1)?)?),
            13 => ExpressionDesc::Setfield(
                self.boxed(f.at(0)?)?,
                self.longident_loc(f.at(1)?)?,
                self.boxed(f.at(2)?)?,
            ),
            14 => ExpressionDesc::Array(self.list(f.at(0)?, |d, e| d.expression(e))?),
            15 => ExpressionDesc::Ifthenelse(
                self.boxed(f.at(0)?)?,
                self.boxed(f.at(1)?)?,
                self.opt_expression(f.at(2)?)?,
            ),
            16 => ExpressionDesc::Sequence(self.boxed(f.at(0)?)?, self.boxed(f.at(1)?)?),
            17 => ExpressionDesc::While(self.boxed(f.at(0)?)?, self.boxed(f.at(1)?)?),
            18 => ExpressionDesc::For(
                Box::new(self.pattern(f.at(0)?)?),
                self.boxed(f.at(1)?)?,
                self.boxed(f.at(2)?)?,
                self.direction_flag(f.at(3)?)?,
                self.boxed(f.at(4)?)?,
            ),
            19 => ExpressionDesc::Constraint(
                self.boxed(f.at(0)?)?,
                Box::new(self.core_type(f.at(1)?)?),
            ),
            20 => ExpressionDesc::Coerce(
                self.boxed(f.at(0)?)?,
                (),
                Box::new(self.core_type(f.at(2)?)?),
            ),
            21 => ExpressionDesc::Send(self.boxed(f.at(0)?)?, self.string_loc(f.at(1)?)?),
            22 => ExpressionDesc::New(self.longident_loc(f.at(0)?)?),
            23 => ExpressionDesc::Setinstvar(self.string_loc(f.at(0)?)?, self.boxed(f.at(1)?)?),
            24 => ExpressionDesc::Override(self.list(f.at(0)?, |d, o| {
                let f = d.fields(o, 2, "override")?;
                Ok((d.string_loc(f.at(0)?)?, d.expression(f.at(1)?)?))
            })?),
            25 => ExpressionDesc::Letmodule(
                self.string_loc(f.at(0)?)?,
                Box::new(self.module_expr(f.at(1)?)?),
                self.boxed(f.at(2)?)?,
            ),
            26 => ExpressionDesc::Letexception(
                self.extension_constructor(f.at(0)?)?,
                self.boxed(f.at(1)?)?,
            ),
            27 => ExpressionDesc::Assert(self.boxed(f.at(0)?)?),
            28 => ExpressionDesc::Lazy(self.boxed(f.at(0)?)?),
            29 => ExpressionDesc::Poly(
                self.boxed(f.at(0)?)?,
                self.option(f.at(1)?, |d, t| d.core_type(t))?.map(Box::new),
            ),
            30 => ExpressionDesc::Object,
            31 => ExpressionDesc::Newtype(self.string_loc(f.at(0)?)?, self.boxed(f.at(1)?)?),
            32 => ExpressionDesc::Pack(Box::new(self.module_expr(f.at(0)?)?)),
            33 => ExpressionDesc::Open(
                self.override_flag(f.at(0)?)?,
                self.longident_loc(f.at(1)?)?,
                self.boxed(f.at(2)?)?,
            ),
            34 => ExpressionDesc::Extension(self.attribute(f.at(0)?)?),
            _ => return err("expression_desc", v),
        })
    }

    fn value_binding(&mut self, v: &OcamlValue) -> R<ValueBinding> {
        let f = self.fields(v, 4, "value_binding")?;
        Ok(ValueBinding {
            pvb_pat: self.pattern(f.at(0)?)?,
            pvb_expr: self.expression(f.at(1)?)?,
            pvb_attributes: self.attributes(f.at(2)?)?,
            pvb_loc: self.location(f.at(3)?)?,
        })
    }

    fn value_description(&mut self, v: &OcamlValue) -> R<ValueDescription> {
        let f = self.fields(v, 5, "value_description")?;
        Ok(ValueDescription {
            pval_name: self.string_loc(f.at(0)?)?,
            pval_type: self.core_type(f.at(1)?)?,
            pval_prim: self.list(f.at(2)?, |d, s| d.string(s))?,
            pval_attributes: self.attributes(f.at(3)?)?,
            pval_loc: self.location(f.at(4)?)?,
        })
    }

    // ========== Type declarations ==========

    fn params(&mut self, v: &OcamlValue) -> R<Vec<(CoreType, Variance)>> {
        self.list(v, |d, p| {
            let f = d.fields(p, 2, "type parameter")?;
            Ok((d.core_type(f.at(0)?)?, d.variance(f.at(1)?)?))
        })
    }

    fn type_declaration(&mut self, v: &OcamlValue) -> R<TypeDeclaration> {
        let f = self.fields(v, 8, "type_declaration")?;
        Ok(TypeDeclaration {
            ptype_name: self.string_loc(f.at(0)?)?,
            ptype_params: self.params(f.at(1)?)?,
            ptype_cstrs: self.list(f.at(2)?, |d, c| {
                let f = d.fields(c, 3, "type constraint")?;
                Ok((
                    d.core_type(f.at(0)?)?,
                    d.core_type(f.at(1)?)?,
                    d.location(f.at(2)?)?,
                ))
            })?,
            ptype_kind: self.type_kind(f.at(3)?)?,
            ptype_private: self.private_flag(f.at(4)?)?,
            ptype_manifest: self.option(f.at(5)?, |d, t| d.core_type(t))?,
            ptype_attributes: self.attributes(f.at(6)?)?,
            ptype_loc: self.location(f.at(7)?)?,
        })
    }

    fn type_kind(&mut self, v: &OcamlValue) -> R<TypeKind> {
        match v {
            OcamlValue::Int(0) => Ok(TypeKind::Abstract),
            OcamlValue::Int(1) => Ok(TypeKind::Open),
            OcamlValue::Block(0, f) if f.len() == 1 => Ok(TypeKind::Variant(
                self.list(f.at(0)?, |d, c| d.constructor_declaration(c))?,
            )),
            OcamlValue::Block(1, f) if f.len() == 1 => Ok(TypeKind::Record(
                self.list(f.at(0)?, |d, l| d.label_declaration(l))?,
            )),
            _ => err("type_kind", v),
        }
    }

    fn label_declaration(&mut self, v: &OcamlValue) -> R<LabelDeclaration> {
        let f = self.fields(v, 5, "label_declaration")?;
        Ok(LabelDeclaration {
            pld_name: self.string_loc(f.at(0)?)?,
            pld_mutable: self.mutable_flag(f.at(1)?)?,
            pld_type: self.core_type(f.at(2)?)?,
            pld_loc: self.location(f.at(3)?)?,
            pld_attributes: self.attributes(f.at(4)?)?,
        })
    }

    fn constructor_declaration(&mut self, v: &OcamlValue) -> R<ConstructorDeclaration> {
        let f = self.fields(v, 5, "constructor_declaration")?;
        Ok(ConstructorDeclaration {
            pcd_name: self.string_loc(f.at(0)?)?,
            pcd_args: self.constructor_arguments(f.at(1)?)?,
            pcd_res: self.option(f.at(2)?, |d, t| d.core_type(t))?,
            pcd_loc: self.location(f.at(3)?)?,
            pcd_attributes: self.attributes(f.at(4)?)?,
        })
    }

    fn constructor_arguments(&mut self, v: &OcamlValue) -> R<ConstructorArguments> {
        let (tag, f) = self.block(v, "constructor_arguments")?;
        Ok(match tag {
            0 => ConstructorArguments::Tuple(self.list(f.at(0)?, |d, t| d.core_type(t))?),
            1 => ConstructorArguments::Record(self.list(f.at(0)?, |d, l| d.label_declaration(l))?),
            _ => return err("constructor_arguments", v),
        })
    }

    fn type_extension(&mut self, v: &OcamlValue) -> R<TypeExtension> {
        let f = self.fields(v, 5, "type_extension")?;
        Ok(TypeExtension {
            ptyext_path: self.longident_loc(f.at(0)?)?,
            ptyext_params: self.params(f.at(1)?)?,
            ptyext_constructors: self.list(f.at(2)?, |d, e| d.extension_constructor(e))?,
            ptyext_private: self.private_flag(f.at(3)?)?,
            ptyext_attributes: self.attributes(f.at(4)?)?,
        })
    }

    fn extension_constructor(&mut self, v: &OcamlValue) -> R<ExtensionConstructor> {
        let f = self.fields(v, 4, "extension_constructor")?;
        Ok(ExtensionConstructor {
            pext_name: self.string_loc(f.at(0)?)?,
            pext_kind: self.extension_constructor_kind(f.at(1)?)?,
            pext_loc: self.location(f.at(2)?)?,
            pext_attributes: self.attributes(f.at(3)?)?,
        })
    }

    fn extension_constructor_kind(&mut self, v: &OcamlValue) -> R<ExtensionConstructorKind> {
        let (tag, f) = self.block(v, "extension_constructor_kind")?;
        Ok(match tag {
            0 => ExtensionConstructorKind::Decl(
                self.constructor_arguments(f.at(0)?)?,
                self.option(f.at(1)?, |d, t| d.core_type(t))?,
            ),
            1 => ExtensionConstructorKind::Rebind(self.longident_loc(f.at(0)?)?),
            _ => return err("extension_constructor_kind", v),
        })
    }

    // ========== Module types ==========

    fn module_type(&mut self, v: &OcamlValue) -> R<ModuleType> {
        let f = self.fields(v, 3, "module_type")?;
        Ok(ModuleType {
            pmty_desc: self.module_type_desc(f.at(0)?)?,
            pmty_loc: self.location(f.at(1)?)?,
            pmty_attributes: self.attributes(f.at(2)?)?,
        })
    }

    fn module_type_desc(&mut self, v: &OcamlValue) -> R<ModuleTypeDesc> {
        let (tag, f) = self.block(v, "module_type_desc")?;
        Ok(match tag {
            0 => ModuleTypeDesc::Ident(self.longident_loc(f.at(0)?)?),
            1 => ModuleTypeDesc::Signature(self.signature(f.at(0)?)?),
            2 => ModuleTypeDesc::Functor(
                self.string_loc(f.at(0)?)?,
                self.option(f.at(1)?, |d, m| d.module_type(m))?
                    .map(Box::new),
                Box::new(self.module_type(f.at(2)?)?),
            ),
            3 => ModuleTypeDesc::With(
                Box::new(self.module_type(f.at(0)?)?),
                self.list(f.at(1)?, |d, c| d.with_constraint(c))?,
            ),
            4 => ModuleTypeDesc::Typeof(Box::new(self.module_expr(f.at(0)?)?)),
            5 => ModuleTypeDesc::Extension(self.attribute(f.at(0)?)?),
            6 => ModuleTypeDesc::Alias(self.longident_loc(f.at(0)?)?),
            _ => return err("module_type_desc", v),
        })
    }

    fn with_constraint(&mut self, v: &OcamlValue) -> R<WithConstraint> {
        let (tag, f) = self.block(v, "with_constraint")?;
        Ok(match tag {
            0 => WithConstraint::Type(
                self.longident_loc(f.at(0)?)?,
                self.type_declaration(f.at(1)?)?,
            ),
            1 => {
                WithConstraint::Module(self.longident_loc(f.at(0)?)?, self.longident_loc(f.at(1)?)?)
            }
            2 => WithConstraint::TypeSubst(
                self.longident_loc(f.at(0)?)?,
                self.type_declaration(f.at(1)?)?,
            ),
            3 => WithConstraint::ModSubst(
                self.longident_loc(f.at(0)?)?,
                self.longident_loc(f.at(1)?)?,
            ),
            _ => return err("with_constraint", v),
        })
    }

    // ========== Signatures ==========

    pub fn signature(&mut self, v: &OcamlValue) -> R<Signature> {
        self.list(v, |d, item| d.signature_item(item))
    }

    fn signature_item(&mut self, v: &OcamlValue) -> R<SignatureItem> {
        let f = self.fields(v, 2, "signature_item")?;
        Ok(SignatureItem {
            psig_desc: self.signature_item_desc(f.at(0)?)?,
            psig_loc: self.location(f.at(1)?)?,
        })
    }

    fn signature_item_desc(&mut self, v: &OcamlValue) -> R<SignatureItemDesc> {
        let (tag, f) = self.block(v, "signature_item_desc")?;
        Ok(match tag {
            0 => SignatureItemDesc::Value(self.value_description(f.at(0)?)?),
            1 => SignatureItemDesc::Type(
                self.rec_flag(f.at(0)?)?,
                self.list(f.at(1)?, |d, t| d.type_declaration(t))?,
            ),
            2 => SignatureItemDesc::Typext(self.type_extension(f.at(0)?)?),
            3 => SignatureItemDesc::Exception(self.extension_constructor(f.at(0)?)?),
            4 => SignatureItemDesc::Module(self.module_declaration(f.at(0)?)?),
            5 => SignatureItemDesc::Recmodule(self.list(f.at(0)?, |d, m| d.module_declaration(m))?),
            6 => SignatureItemDesc::Modtype(self.module_type_declaration(f.at(0)?)?),
            7 => SignatureItemDesc::Open(self.open_description(f.at(0)?)?),
            8 => SignatureItemDesc::Include(self.include_infos(f.at(0)?, |d, m| d.module_type(m))?),
            9 => SignatureItemDesc::Class,
            10 => SignatureItemDesc::ClassType,
            11 => SignatureItemDesc::Attribute(self.attribute(f.at(0)?)?),
            12 => {
                SignatureItemDesc::Extension(self.attribute(f.at(0)?)?, self.attributes(f.at(1)?)?)
            }
            _ => return err("signature_item_desc", v),
        })
    }

    fn module_declaration(&mut self, v: &OcamlValue) -> R<ModuleDeclaration> {
        let f = self.fields(v, 4, "module_declaration")?;
        Ok(ModuleDeclaration {
            pmd_name: self.string_loc(f.at(0)?)?,
            pmd_type: self.module_type(f.at(1)?)?,
            pmd_attributes: self.attributes(f.at(2)?)?,
            pmd_loc: self.location(f.at(3)?)?,
        })
    }

    fn module_type_declaration(&mut self, v: &OcamlValue) -> R<ModuleTypeDeclaration> {
        let f = self.fields(v, 4, "module_type_declaration")?;
        Ok(ModuleTypeDeclaration {
            pmtd_name: self.string_loc(f.at(0)?)?,
            pmtd_type: self.option(f.at(1)?, |d, m| d.module_type(m))?,
            pmtd_attributes: self.attributes(f.at(2)?)?,
            pmtd_loc: self.location(f.at(3)?)?,
        })
    }

    fn open_description(&mut self, v: &OcamlValue) -> R<OpenDescription> {
        let f = self.fields(v, 4, "open_description")?;
        Ok(OpenDescription {
            popen_lid: self.longident_loc(f.at(0)?)?,
            popen_override: self.override_flag(f.at(1)?)?,
            popen_loc: self.location(f.at(2)?)?,
            popen_attributes: self.attributes(f.at(3)?)?,
        })
    }

    fn include_infos<A>(
        &mut self,
        v: &OcamlValue,
        f: impl FnOnce(&mut Self, &OcamlValue) -> R<A>,
    ) -> R<IncludeInfos<A>> {
        let fields = self.fields(v, 3, "include_infos")?;
        Ok(IncludeInfos {
            pincl_mod: f(self, &fields[0])?,
            pincl_loc: self.location(&fields[1])?,
            pincl_attributes: self.attributes(&fields[2])?,
        })
    }

    // ========== Module expressions ==========

    fn module_expr(&mut self, v: &OcamlValue) -> R<ModuleExpr> {
        let f = self.fields(v, 3, "module_expr")?;
        Ok(ModuleExpr {
            pmod_desc: self.module_expr_desc(f.at(0)?)?,
            pmod_loc: self.location(f.at(1)?)?,
            pmod_attributes: self.attributes(f.at(2)?)?,
        })
    }

    fn module_expr_desc(&mut self, v: &OcamlValue) -> R<ModuleExprDesc> {
        let (tag, f) = self.block(v, "module_expr_desc")?;
        Ok(match tag {
            0 => ModuleExprDesc::Ident(self.longident_loc(f.at(0)?)?),
            1 => ModuleExprDesc::Structure(self.structure(f.at(0)?)?),
            2 => ModuleExprDesc::Functor(
                self.string_loc(f.at(0)?)?,
                self.option(f.at(1)?, |d, m| d.module_type(m))?
                    .map(Box::new),
                Box::new(self.module_expr(f.at(2)?)?),
            ),
            3 => ModuleExprDesc::Apply(
                Box::new(self.module_expr(f.at(0)?)?),
                Box::new(self.module_expr(f.at(1)?)?),
            ),
            4 => ModuleExprDesc::Constraint(
                Box::new(self.module_expr(f.at(0)?)?),
                Box::new(self.module_type(f.at(1)?)?),
            ),
            5 => ModuleExprDesc::Unpack(self.boxed(f.at(0)?)?),
            6 => ModuleExprDesc::Extension(self.attribute(f.at(0)?)?),
            _ => return err("module_expr_desc", v),
        })
    }

    // ========== Structures ==========

    pub fn structure(&mut self, v: &OcamlValue) -> R<Structure> {
        self.list(v, |d, item| d.structure_item(item))
    }

    fn structure_item(&mut self, v: &OcamlValue) -> R<StructureItem> {
        let f = self.fields(v, 2, "structure_item")?;
        Ok(StructureItem {
            pstr_desc: self.structure_item_desc(f.at(0)?)?,
            pstr_loc: self.location(f.at(1)?)?,
        })
    }

    fn structure_item_desc(&mut self, v: &OcamlValue) -> R<StructureItemDesc> {
        let (tag, f) = self.block(v, "structure_item_desc")?;
        Ok(match tag {
            0 => StructureItemDesc::Eval(self.expression(f.at(0)?)?, self.attributes(f.at(1)?)?),
            1 => StructureItemDesc::Value(
                self.rec_flag(f.at(0)?)?,
                self.list(f.at(1)?, |d, vb| d.value_binding(vb))?,
            ),
            2 => StructureItemDesc::Primitive(self.value_description(f.at(0)?)?),
            3 => StructureItemDesc::Type(
                self.rec_flag(f.at(0)?)?,
                self.list(f.at(1)?, |d, t| d.type_declaration(t))?,
            ),
            4 => StructureItemDesc::Typext(self.type_extension(f.at(0)?)?),
            5 => StructureItemDesc::Exception(self.extension_constructor(f.at(0)?)?),
            6 => StructureItemDesc::Module(self.module_binding(f.at(0)?)?),
            7 => StructureItemDesc::Recmodule(self.list(f.at(0)?, |d, m| d.module_binding(m))?),
            8 => StructureItemDesc::Modtype(self.module_type_declaration(f.at(0)?)?),
            9 => StructureItemDesc::Open(self.open_description(f.at(0)?)?),
            10 => StructureItemDesc::Class,
            11 => StructureItemDesc::ClassType,
            12 => {
                StructureItemDesc::Include(self.include_infos(f.at(0)?, |d, m| d.module_expr(m))?)
            }
            13 => StructureItemDesc::Attribute(self.attribute(f.at(0)?)?),
            14 => {
                StructureItemDesc::Extension(self.attribute(f.at(0)?)?, self.attributes(f.at(1)?)?)
            }
            _ => return err("structure_item_desc", v),
        })
    }

    fn module_binding(&mut self, v: &OcamlValue) -> R<ModuleBinding> {
        let f = self.fields(v, 4, "module_binding")?;
        Ok(ModuleBinding {
            pmb_name: self.string_loc(f.at(0)?)?,
            pmb_expr: self.module_expr(f.at(1)?)?,
            pmb_attributes: self.attributes(f.at(2)?)?,
            pmb_loc: self.location(f.at(3)?)?,
        })
    }
}

/// An external PPX's output file (`cmd_ppx_apply.ml` `read_ast`): the magic,
/// the marshaled input name, then the marshaled Parsetree0 AST.
pub struct PpxOutput {
    pub input_name: String,
    pub ast: OcamlValue,
}

/// Read the binary protocol written by an external PPX.
pub fn read_ppx_output(data: &[u8], magic: &[u8]) -> Result<PpxOutput, DecodeError> {
    use crate::cmi::marshal_reader::MarshalReader;
    if data.len() < magic.len() || &data[..magic.len()] != magic {
        return Err(DecodeError("wrong magic number".to_string()));
    }
    let mut cursor = std::io::Cursor::new(&data[magic.len()..]);
    let input_name = MarshalReader::new()
        .read_with_header(&mut cursor)
        .map_err(|e| DecodeError(e.to_string()))?;
    let ast = MarshalReader::new()
        .read_with_header(&mut cursor)
        .map_err(|e| DecodeError(e.to_string()))?;
    let OcamlValue::String(input_name) = input_name else {
        return Err(DecodeError("expected the input file name".to_string()));
    };
    Ok(PpxOutput { input_name, ast })
}
