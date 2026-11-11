//! Exact key encoding for `Lambda.make_key` (`compiler/ml/lambda.ml:432-466`).
//!
//! OCaml compares normalized terms with structural equality. Rust writes
//! each normalized term as a string, and two terms are equal when their
//! strings are. Payloads (constants, primitives, apply and switch metadata)
//! are written with [`KeyEncode`], a self-delimiting encoding: integers end
//! in `;`, strings are length-prefixed, enums write their variant index and
//! then their fields, `Option`s are tagged and sequences counted. A
//! concatenation of self-delimiting codes is injective, so two payloads
//! encode equally exactly when they are equal. None of these types holds a
//! float, so that is also exactly when their derived `Debug` text, which the
//! keys used before, is equal. A type with a hand-written `Debug` keeps that
//! text, length-prefixed, so its equality classes do not change.
//!
//! The `impl`s below follow the type definitions field by field and match
//! every variant, so a new field or variant is a compile error here.

/// Sink for `MakeKeyWriter`: builds the key, or compares it with an
/// expected key as it is written.
pub(super) struct KeyOut<'e> {
    pub(super) buf: String,
    expect: Option<&'e str>,
    pos: usize,
    pub(super) diverged: bool,
}

impl<'e> KeyOut<'e> {
    pub(super) fn new(capacity: usize) -> Self {
        KeyOut {
            buf: String::with_capacity(capacity),
            expect: None,
            pos: 0,
            diverged: false,
        }
    }

    pub(super) fn expecting(key: &'e str) -> Self {
        KeyOut {
            buf: String::new(),
            expect: Some(key),
            pos: 0,
            diverged: false,
        }
    }

    pub(super) fn push_str(&mut self, s: &str) {
        match self.expect {
            None => self.buf.push_str(s),
            Some(key) => {
                if !self.diverged
                    && key.as_bytes().get(self.pos..self.pos + s.len()) == Some(s.as_bytes())
                {
                    self.pos += s.len();
                } else {
                    self.diverged = true;
                }
            }
        }
    }

    pub(super) fn push(&mut self, c: char) {
        self.push_str(c.encode_utf8(&mut [0; 4]));
    }

    pub(super) fn matches_all(&self) -> bool {
        !self.diverged && self.expect.is_some_and(|key| key.len() == self.pos)
    }

    /// A signed integer in decimal, ended by `;`.
    pub(super) fn int(&mut self, value: i128) {
        let mut buf = [0u8; 41];
        let mut i = buf.len() - 1;
        buf[i] = b';';
        let mut n = value.unsigned_abs();
        loop {
            i -= 1;
            buf[i] = b'0' + (n % 10) as u8;
            n /= 10;
            if n == 0 {
                break;
            }
        }
        if value < 0 {
            i -= 1;
            buf[i] = b'-';
        }
        self.push_str(std::str::from_utf8(&buf[i..]).expect("ASCII digits"));
    }

    /// An enum variant index.
    pub(super) fn tag(&mut self, index: u32) {
        self.int(i128::from(index));
    }

    /// A string, prefixed by its byte length.
    pub(super) fn str(&mut self, s: &str) {
        self.int(s.len() as i128);
        self.push_str(s);
    }

    /// A value whose `Debug` impl is hand-written, by its `Debug` text.
    pub(super) fn debug(&mut self, value: &impl std::fmt::Debug) {
        self.str(&format!("{value:?}"));
    }
}

impl std::fmt::Write for KeyOut<'_> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.push_str(s);
        if self.diverged {
            Err(std::fmt::Error)
        } else {
            Ok(())
        }
    }
}

/// Exact, self-delimiting key encoding of a `make_key` payload.
pub(super) trait KeyEncode {
    fn encode(&self, out: &mut KeyOut<'_>);
}

macro_rules! int_key {
    ($($t:ty),*) => {$(
        impl KeyEncode for $t {
            fn encode(&self, out: &mut KeyOut<'_>) {
                out.int(i128::from(*self));
            }
        }
    )*};
}
int_key!(i8, i16, i32, i64, u8, u16, u32, u64);

impl KeyEncode for usize {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.int(*self as i128);
    }
}

impl KeyEncode for bool {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.push(if *self { 't' } else { 'f' });
    }
}

impl KeyEncode for char {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.int(i128::from(u32::from(*self)));
    }
}

impl KeyEncode for str {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.str(self);
    }
}

impl KeyEncode for String {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.str(self);
    }
}

impl<T: KeyEncode + ?Sized> KeyEncode for &T {
    fn encode(&self, out: &mut KeyOut<'_>) {
        (**self).encode(out);
    }
}

impl<T: KeyEncode + ?Sized> KeyEncode for Box<T> {
    fn encode(&self, out: &mut KeyOut<'_>) {
        (**self).encode(out);
    }
}

impl<T: KeyEncode> KeyEncode for Option<T> {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            None => out.push('N'),
            Some(value) => {
                out.push('S');
                value.encode(out);
            }
        }
    }
}

impl<T: KeyEncode> KeyEncode for [T] {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.int(self.len() as i128);
        for item in self {
            item.encode(out);
        }
    }
}

impl<T: KeyEncode> KeyEncode for Vec<T> {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.as_slice().encode(out);
    }
}

impl<A: KeyEncode, B: KeyEncode> KeyEncode for (A, B) {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.0.encode(out);
        self.1.encode(out);
    }
}

impl KeyEncode for crate::ident::Ident {
    fn encode(&self, out: &mut KeyOut<'_>) {
        out.debug(self);
    }
}

impl KeyEncode for crate::lambda::lam_compat::Comparison {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Eq => out.tag(0),
            Self::Neq => out.tag(1),
            Self::Lt => out.tag(2),
            Self::Gt => out.tag(3),
            Self::Le => out.tag(4),
            Self::Ge => out.tag(5),
        }
    }
}

impl KeyEncode for crate::lambda::lam_compat::FieldDbgInfo {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Record { name } => {
                out.tag(0);
                name.encode(out);
            }
            Self::Module { name } => {
                out.tag(1);
                name.encode(out);
            }
            Self::RecordInline { name } => {
                out.tag(2);
                name.encode(out);
            }
            Self::RecordExtension { name } => {
                out.tag(3);
                name.encode(out);
            }
            Self::Tuple => out.tag(4),
            Self::PolyVarTag => out.tag(5),
            Self::PolyVarContent => out.tag(6),
            Self::Extension => out.tag(7),
            Self::Variant => out.tag(8),
            Self::VariantTag => out.tag(9),
            Self::Cons => out.tag(10),
        }
    }
}

impl KeyEncode for crate::lambda::lam_compat::LetKind {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Strict => out.tag(0),
            Self::Alias => out.tag(1),
            Self::StrictOpt => out.tag(2),
            Self::Variable => out.tag(3),
        }
    }
}

impl KeyEncode for crate::lambda::lam_compat::SetFieldDbgInfo {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::RecordSet(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::RecordInlineSet(f0) => {
                out.tag(1);
                f0.encode(out);
            }
            Self::RecordExtensionSet(f0) => {
                out.tag(2);
                f0.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::lambda::lam_constant::Constant {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::JsNull => out.tag(0),
            Self::JsUndefined { is_unit } => {
                out.tag(1);
                is_unit.encode(out);
            }
            Self::JsTrue => out.tag(2),
            Self::JsFalse => out.tag(3),
            Self::Int { i, comment } => {
                out.tag(4);
                i.encode(out);
                comment.encode(out);
            }
            Self::NativeInt { i, comment } => {
                out.tag(5);
                i.encode(out);
                comment.encode(out);
            }
            Self::Constructor(f0) => {
                out.tag(6);
                f0.encode(out);
            }
            Self::Char(f0) => {
                out.tag(7);
                f0.encode(out);
            }
            Self::String(f0) => {
                out.tag(8);
                f0.encode(out);
            }
            Self::ImmString(f0) => {
                out.tag(9);
                f0.encode(out);
            }
            Self::Float(f0) => {
                out.tag(10);
                f0.encode(out);
            }
            Self::BigInt { negative, value } => {
                out.tag(11);
                negative.encode(out);
                value.encode(out);
            }
            Self::Pointer(f0) => {
                out.tag(12);
                f0.encode(out);
            }
            Self::Block { tag_info, elements } => {
                out.tag(13);
                tag_info.encode(out);
                elements.encode(out);
            }
            Self::Some(f0) => {
                out.tag(14);
                f0.encode(out);
            }
            Self::ModuleAlias => out.tag(15),
        }
    }
}

impl KeyEncode for crate::lambda::lam_constant::ConstructorRuntimeTag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Int(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::String(f0) => {
                out.tag(1);
                f0.encode(out);
            }
            Self::Float(f0) => {
                out.tag(2);
                f0.encode(out);
            }
            Self::BigInt(f0) => {
                out.tag(3);
                f0.encode(out);
            }
            Self::Bool(f0) => {
                out.tag(4);
                f0.encode(out);
            }
            Self::Null => out.tag(5),
            Self::Undefined => out.tag(6),
        }
    }
}

impl KeyEncode for crate::lambda::lam_constant::ConstructorTag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.name.encode(out);
        self.const_.encode(out);
        self.non_const.encode(out);
        self.runtime_tag.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_constant::PointerInfo {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::None => out.tag(0),
            Self::Constructor(f0) => {
                out.tag(1);
                f0.encode(out);
            }
            Self::ShapeNone => out.tag(2),
            Self::AssertFalse => out.tag(3),
            Self::Some(f0) => {
                out.tag(4);
                f0.encode(out);
            }
            Self::PolyVariant(f0) => {
                out.tag(5);
                f0.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::lambda::lam_primitive::ImportSource {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::ImportModule { module_, path } => {
                out.tag(0);
                module_.encode(out);
                path.encode(out);
            }
            Self::ImportExternal { module_, path } => {
                out.tag(1);
                module_.encode(out);
                path.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::lambda::lam_primitive::JsCall {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.prim_name.encode(out);
        self.arg_types.encode(out);
        self.ffi.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_primitive::JsxElement {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.jsx_name.encode(out);
        self.jsx_ffi.encode(out);
        self.jsx_multi.encode(out);
        self.jsx_fragment.encode(out);
        self.jsx_spread.encode(out);
        self.jsx_props.encode(out);
        self.jsx_children.encode(out);
        self.jsx_key.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_primitive::JsRawInfo {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.code.encode(out);
        self.is_stmt.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_primitive::Mutable {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Mutable => out.tag(0),
            Self::Immutable => out.tag(1),
        }
    }
}

impl KeyEncode for crate::lambda::lam_primitive::Primitive {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Pmakeblock(f0, f1) => {
                out.tag(0);
                f0.encode(out);
                f1.encode(out);
            }
            Self::Pfield(f0, f1) => {
                out.tag(1);
                f0.encode(out);
                f1.encode(out);
            }
            Self::Psetfield(f0, f1) => {
                out.tag(2);
                f0.encode(out);
                f1.encode(out);
            }
            Self::Pduprecord => out.tag(3),
            Self::PrecordRest(f0) => {
                out.tag(4);
                f0.encode(out);
            }
            Self::PtaggedTemplate(f0) => {
                out.tag(5);
                f0.encode(out);
            }
            Self::Ptemplate(f0) => {
                out.tag(6);
                f0.encode(out);
            }
            Self::PjsCall(f0) => {
                out.tag(7);
                f0.encode(out);
            }
            Self::PjsObjectCreate(f0) => {
                out.tag(8);
                f0.encode(out);
            }
            Self::Praise => out.tag(9),
            Self::Pobjcomp(f0) => {
                out.tag(10);
                f0.encode(out);
            }
            Self::Pobjorder => out.tag(11),
            Self::Pobjmin => out.tag(12),
            Self::Pobjmax => out.tag(13),
            Self::Pobjtag => out.tag(14),
            Self::Pobjsize => out.tag(15),
            Self::Psequand => out.tag(16),
            Self::Psequor => out.tag(17),
            Self::Pnot => out.tag(18),
            Self::Pboolcomp(f0) => {
                out.tag(19);
                f0.encode(out);
            }
            Self::Pboolorder => out.tag(20),
            Self::Pboolmin => out.tag(21),
            Self::Pboolmax => out.tag(22),
            Self::Pnegint => out.tag(24),
            Self::Paddint => out.tag(25),
            Self::Psubint => out.tag(26),
            Self::Pmulint => out.tag(27),
            Self::Pdivint => out.tag(28),
            Self::Pmodint => out.tag(29),
            Self::Ppowint => out.tag(30),
            Self::Pandint => out.tag(31),
            Self::Porint => out.tag(32),
            Self::Pxorint => out.tag(33),
            Self::Pnotint => out.tag(34),
            Self::Plslint => out.tag(35),
            Self::Plsrint => out.tag(36),
            Self::Pasrint => out.tag(37),
            Self::Pintcomp(f0) => {
                out.tag(38);
                f0.encode(out);
            }
            Self::Pintorder => out.tag(39),
            Self::Pintmin => out.tag(40),
            Self::Pintmax => out.tag(41),
            Self::Pintoffloat => out.tag(42),
            Self::Pfloatofint => out.tag(43),
            Self::Pnegfloat => out.tag(44),
            Self::Paddfloat => out.tag(45),
            Self::Psubfloat => out.tag(46),
            Self::Pmulfloat => out.tag(47),
            Self::Pdivfloat => out.tag(48),
            Self::Pmodfloat => out.tag(49),
            Self::Ppowfloat => out.tag(50),
            Self::Pfloatcomp(f0) => {
                out.tag(51);
                f0.encode(out);
            }
            Self::Pfloatorder => out.tag(52),
            Self::Pfloatmin => out.tag(53),
            Self::Pfloatmax => out.tag(54),
            Self::Pnegbigint => out.tag(55),
            Self::Paddbigint => out.tag(56),
            Self::Psubbigint => out.tag(57),
            Self::Pmulbigint => out.tag(58),
            Self::Pdivbigint => out.tag(59),
            Self::Pmodbigint => out.tag(60),
            Self::Ppowbigint => out.tag(61),
            Self::Pandbigint => out.tag(62),
            Self::Porbigint => out.tag(63),
            Self::Pxorbigint => out.tag(64),
            Self::Pnotbigint => out.tag(65),
            Self::Plslbigint => out.tag(66),
            Self::Pasrbigint => out.tag(67),
            Self::Pbigintcomp(f0) => {
                out.tag(68);
                f0.encode(out);
            }
            Self::Pbigintorder => out.tag(69),
            Self::Pbigintmin => out.tag(70),
            Self::Pbigintmax => out.tag(71),
            Self::Pstringlength => out.tag(72),
            Self::Pstringrefu => out.tag(73),
            Self::Pstringrefs => out.tag(74),
            Self::Pstringadd => out.tag(75),
            Self::Pstringcomp(f0) => {
                out.tag(76);
                f0.encode(out);
            }
            Self::Pstringorder => out.tag(77),
            Self::Pstringmin => out.tag(78),
            Self::Pstringmax => out.tag(79),
            Self::Pmakearray => out.tag(80),
            Self::Parraylength => out.tag(81),
            Self::Parrayrefu => out.tag(82),
            Self::Parraysetu => out.tag(83),
            Self::Parrayrefs => out.tag(84),
            Self::Pmakelist => out.tag(86),
            Self::Pmakedict => out.tag(87),
            Self::PdictHas => out.tag(88),
            Self::Pjsx(f0) => {
                out.tag(121);
                f0.encode(out);
            }
            Self::PdictSpread => out.tag(122),
            Self::ParraySpread => out.tag(123),
            Self::PlistSpread => out.tag(124),
            Self::Pawait => out.tag(89),
            Self::Pidentity => out.tag(90),
            Self::Pignore => out.tag(91),
            Self::PisPolyVarBlock => out.tag(92),
            Self::Pjscomp(f0) => {
                out.tag(93);
                f0.encode(out);
            }
            Self::PjsApply => out.tag(94),
            Self::Pdebugger => out.tag(95),
            Self::PjsObjectGet(f0) => {
                out.tag(96);
                f0.encode(out);
            }
            Self::PjsObjectSet(f0) => {
                out.tag(97);
                f0.encode(out);
            }
            Self::PinitMod => out.tag(98),
            Self::PupdateMod => out.tag(99),
            Self::PrawJsCode(f0) => {
                out.tag(100);
                f0.encode(out);
            }
            Self::PjsFnMethod => out.tag(101),
            Self::PnullToOpt => out.tag(102),
            Self::PnullUndefinedToOpt => out.tag(103),
            Self::PisNull => out.tag(104),
            Self::PisUndefined => out.tag(105),
            Self::PisNullUndefined => out.tag(106),
            Self::Pimport(f0) => {
                out.tag(107);
                f0.encode(out);
            }
            Self::Ptypeof => out.tag(108),
            Self::PfnArity => out.tag(109),
            Self::PcreateExtension(f0) => {
                out.tag(110);
                f0.encode(out);
            }
            Self::PextensionSlotEq => out.tag(111),
            Self::PisNotNone => out.tag(112),
            Self::PvalFromOption => out.tag(113),
            Self::PvalFromOptionNotNest => out.tag(114),
            Self::Psome => out.tag(115),
            Self::PsomeNotNest => out.tag(116),
            Self::Phash => out.tag(117),
            Self::PhashMixstring => out.tag(118),
            Self::PhashMixint => out.tag(119),
            Self::PhashFinalmix => out.tag(120),
        }
    }
}

impl KeyEncode for crate::lambda::lam_tag_info::ConstructorTag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.name.encode(out);
        self.num_nonconst.encode(out);
        self.runtime.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_tag_info::RecordInlinedTag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.name.encode(out);
        self.num_nonconst.encode(out);
        self.fields.encode(out);
        self.logical_field_count.encode(out);
        self.mutable_flag.encode(out);
        self.runtime.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_tag_info::RecordTag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.fields.encode(out);
        self.logical_field_count.encode(out);
        self.mutable_flag.encode(out);
    }
}

impl KeyEncode for crate::lambda::lam_tag_info::TagInfo {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Constructor(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::RecordInlined(f0) => {
                out.tag(1);
                f0.encode(out);
            }
            Self::Tuple => out.tag(2),
            Self::PolyVar(f0) => {
                out.tag(3);
                f0.encode(out);
            }
            Self::Record(f0) => {
                out.tag(4);
                f0.encode(out);
            }
            Self::Module(f0) => {
                out.tag(5);
                f0.encode(out);
            }
            Self::ModuleExport(f0) => {
                out.tag(6);
                f0.encode(out);
            }
            Self::Extension => out.tag(7),
            Self::Some => out.tag(8),
            Self::SomeNotNested => out.tag(9),
            Self::RecordExt {
                fields,
                mutable_flag,
            } => {
                out.tag(10);
                fields.encode(out);
                mutable_flag.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::lambda::ApplyStatus {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Na => out.tag(0),
            Self::InferFull => out.tag(1),
            Self::Uncurry => out.tag(2),
        }
    }
}

impl KeyEncode for crate::lambda::InlineAttribute {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Always => out.tag(0),
            Self::Never => out.tag(1),
            Self::Default => out.tag(2),
        }
    }
}

impl KeyEncode for crate::lambda::SwitchDispatch {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Direct => out.tag(0),
            Self::Variant(f0) => {
                out.tag(1);
                f0.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::parser::ast::MutableFlag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Immutable => out.tag(0),
            Self::Mutable => out.tag(1),
        }
    }
}

impl KeyEncode for crate::string_literal::StringLiteral {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Valid { source, semantic } => {
                out.tag(0);
                source.encode(out);
                semantic.encode(out);
            }
            Self::InvalidSource(f0) => {
                out.tag(1);
                f0.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::Attr {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::PolyVarString { descr } => {
                out.tag(0);
                descr.encode(out);
            }
            Self::PolyVar { descr } => {
                out.tag(1);
                descr.encode(out);
            }
            Self::Int(f0) => {
                out.tag(2);
                f0.encode(out);
            }
            Self::ArgCst(f0) => {
                out.tag(3);
                f0.encode(out);
            }
            Self::ExternUnit => out.tag(4),
            Self::Nothing => out.tag(5),
            Self::Ignore => out.tag(6),
            Self::Unwrap => out.tag(7),
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::Cst {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::ArgIntLit(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::ArgStringLit(f0) => {
                out.tag(1);
                f0.encode(out);
            }
            Self::ArgJsonLit(f0) => {
                out.tag(2);
                f0.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::DeclKind {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::DeclVal { name } => {
                out.tag(0);
                name.encode(out);
            }
            Self::DeclSend { name } => {
                out.tag(1);
                name.encode(out);
            }
            Self::DeclNew { name } => {
                out.tag(2);
                name.encode(out);
            }
            Self::DeclGet { name } => {
                out.tag(3);
                name.encode(out);
            }
            Self::DeclSet { name } => {
                out.tag(4);
                name.encode(out);
            }
            Self::DeclGetIndex => out.tag(5),
            Self::DeclSetIndex => out.tag(6),
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::ExternalDecl {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.kind.encode(out);
        self.module_.encode(out);
        self.scopes.encode(out);
        self.variadic.encode(out);
        self.effective_arity.encode(out);
    }
}

impl KeyEncode for crate::types::external_ffi_types::ExternalModuleName {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.bundle.encode(out);
        self.module_bind_name.encode(out);
        self.import_attributes.encode(out);
    }
}

impl KeyEncode for crate::types::external_ffi_types::Label {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::ObjEmpty => out.tag(0),
            Self::ObjLabel { name } => {
                out.tag(1);
                name.encode(out);
            }
            Self::ObjOptional {
                name,
                for_sure_no_nested_option,
            } => {
                out.tag(2);
                name.encode(out);
                for_sure_no_nested_option.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::LabelNoname {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::ArgLabel => out.tag(0),
            Self::ArgEmpty => out.tag(1),
            Self::ArgOptional => out.tag(2),
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::ModuleBindName {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::PhintName(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::PhintNothing => out.tag(1),
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::ModuleSource {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::ModuleNamed(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::ModuleItself => out.tag(1),
        }
    }
}

impl KeyEncode for crate::types::external_ffi_types::ObjParam {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.obj_arg_type.encode(out);
        self.obj_arg_label.encode(out);
    }
}

impl KeyEncode for crate::types::external_ffi_types::Param {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.arg_type.encode(out);
        self.arg_label.encode(out);
    }
}

impl KeyEncode for crate::types::variant_runtime::Block {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Tagged(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::Untagged { tag, block_type } => {
                out.tag(1);
                tag.encode(out);
                block_type.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::types::variant_runtime::BlockType {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Number => out.tag(0),
            Self::String => out.tag(1),
            Self::Bigint => out.tag(3),
            Self::Boolean => out.tag(4),
            Self::Instance(f0) => {
                out.tag(5);
                f0.encode(out);
            }
            Self::Function => out.tag(6),
            Self::Object => out.tag(7),
            Self::Unknown => out.tag(8),
            Self::Symbol => out.tag(9),
        }
    }
}

/// Encodes what `Instance`'s equality compares: an array's shape
/// allocation and a class's blocks are not part of the value.
impl KeyEncode for crate::types::variant_runtime::Instance {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Array(_) => out.tag(0),
            Self::Class {
                name, ancestors, ..
            } => {
                out.tag(1);
                name.encode(out);
                ancestors.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::types::variant_runtime::LiteralTag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::String(f0) => {
                out.tag(0);
                f0.encode(out);
            }
            Self::Int(f0) => {
                out.tag(1);
                f0.encode(out);
            }
            Self::Float(f0) => {
                out.tag(2);
                f0.encode(out);
            }
            Self::BigInt(f0) => {
                out.tag(3);
                f0.encode(out);
            }
            Self::Bool(f0) => {
                out.tag(4);
                f0.encode(out);
            }
            Self::Null => out.tag(5),
            Self::Undefined => out.tag(6),
        }
    }
}

impl KeyEncode for crate::types::variant_runtime::MatchingFacts {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.tag_name.encode(out);
        self.block_types.encode(out);
        self.literal_tags.encode(out);
        self.object_cases.encode(out);
    }
}

impl KeyEncode for crate::types::variant_runtime::ObjectCase {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.name.encode(out);
        self.test.encode(out);
    }
}

impl KeyEncode for crate::types::variant_runtime::FieldCheck {
    fn encode(&self, out: &mut KeyOut<'_>) {
        match self {
            Self::Present(field) => {
                out.tag(0);
                field.encode(out);
            }
            Self::Literals(field, literals) => {
                out.tag(1);
                field.encode(out);
                literals.encode(out);
            }
            Self::Kind(field, kind) => {
                out.tag(2);
                field.encode(out);
                kind.encode(out);
            }
        }
    }
}

impl KeyEncode for crate::types::variant_runtime::Tag {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.name.encode(out);
        self.literal.encode(out);
    }
}

impl KeyEncode for crate::types::variant_runtime::TaggedBlock {
    fn encode(&self, out: &mut KeyOut<'_>) {
        self.tag.encode(out);
        self.tag_name.encode(out);
    }
}

#[cfg(test)]
mod tests {
    use super::{KeyEncode, KeyOut};
    use crate::ident::Ident;
    use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
    use crate::lambda::lam_constant::{Constant, PointerInfo};
    use crate::lambda::lam_primitive::{Mutable, Primitive};
    use crate::lambda::lam_tag_info::TagInfo;

    fn key(value: &impl KeyEncode) -> String {
        let mut out = KeyOut::new(16);
        value.encode(&mut out);
        out.buf
    }

    #[test]
    fn encoding_is_self_delimiting() {
        // Shapes that run together when written without delimiters.
        let strings = [
            vec![],
            vec!["".to_string()],
            vec!["ab".to_string()],
            vec!["a".to_string(), "b".to_string()],
            vec!["1;a".to_string()],
            vec!["1".to_string(), "a".to_string()],
        ];
        let keys: Vec<String> = strings.iter().map(key).collect();
        for (i, a) in keys.iter().enumerate() {
            for b in &keys[i + 1..] {
                assert_ne!(a, b);
            }
        }
        assert_ne!(key(&None::<String>), key(&Some(String::new())));
        assert_ne!(key(&(-1i32)), key(&1i32));
        assert_ne!(key(&(12i32, 3i32)), key(&(1i32, 23i32)));
        assert_eq!(key(&i64::MIN), format!("{};", i64::MIN));
    }

    /// Equal keys exactly when the derived `Debug` texts, which `make_key`
    /// compared before, are equal.
    #[test]
    fn same_classes_as_debug() {
        let x = Ident::create_local("x");
        let field = |name: &str| FieldDbgInfo::Record {
            name: crate::name::Name::new(name),
        };
        let prims = [
            Primitive::Paddint,
            Primitive::Psubint,
            Primitive::Pintcomp(Comparison::Eq),
            Primitive::Pintcomp(Comparison::Neq),
            Primitive::Pfield(0, field("a")),
            Primitive::Pfield(0, field("a")),
            Primitive::Pfield(1, field("a")),
            Primitive::Pfield(0, field("b")),
            Primitive::Pfield(0, FieldDbgInfo::Tuple),
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Mutable),
            Primitive::Pmakeblock(TagInfo::Module(vec!["a".into()]), Mutable::Immutable),
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["a".into(), "".into()]),
                Mutable::Immutable,
            ),
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![x]), Mutable::Immutable),
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![x]), Mutable::Immutable),
            Primitive::Pmakeblock(
                TagInfo::ModuleExport(vec![Ident::create_local("x")]),
                Mutable::Immutable,
            ),
            Primitive::PjsObjectGet("a\"b".into()),
            Primitive::PjsObjectGet("a\\\"b".into()),
            Primitive::PjsObjectSet("a\"b".into()),
        ];
        let consts = [
            Constant::int(1),
            Constant::int(1),
            Constant::int(-1),
            Constant::int_with_comment(1, PointerInfo::Some("a".into())),
            Constant::int_with_comment(1, PointerInfo::PolyVariant("a".into())),
            Constant::String("1".into()),
            Constant::ImmString("1".into()),
            Constant::Float("1.".into()),
            Constant::Float("1.0".into()),
            Constant::Some(Box::new(Constant::JsNull)),
            Constant::JsUndefined { is_unit: true },
            Constant::JsUndefined { is_unit: false },
        ];
        fn check<T: KeyEncode + std::fmt::Debug>(values: &[T]) {
            for a in values {
                for b in values {
                    assert_eq!(
                        key(a) == key(b),
                        format!("{a:?}") == format!("{b:?}"),
                        "{a:?} vs {b:?}"
                    );
                }
            }
        }
        check(&prims);
        check(&consts);
    }
}
