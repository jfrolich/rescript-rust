//! Immutable spelling and runtime-equality metadata, populated before planning.
use crate::types::variant_runtime::{BlockType, Instance, LiteralTag};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TextId(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct LiteralId(pub(crate) u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct InstanceId(pub(crate) u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Literal {
    String(TextId),
    Int(i64),
    Float(TextId),
    BigInt(TextId),
    Bool(bool),
    Null,
    Undefined,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Kind {
    Number,
    String,
    Bigint,
    Boolean,
    Instance(InstanceId),
    Symbol,
    Function,
    Object,
    Unknown,
}
impl Kind {
    pub(crate) fn typeof_name(self) -> Option<&'static str> {
        match self {
            Self::Number => Some("number"),
            Self::String => Some("string"),
            Self::Bigint => Some("bigint"),
            Self::Boolean => Some("boolean"),
            Self::Symbol => Some("symbol"),
            Self::Function => Some("function"),
            Self::Object => Some("object"),
            _ => None,
        }
    }
    pub(crate) fn block_type(self) -> BlockType {
        match self {
            Self::Number => BlockType::Number,
            Self::String => BlockType::String,
            Self::Bigint => BlockType::Bigint,
            Self::Boolean => BlockType::Boolean,
            Self::Symbol => BlockType::Symbol,
            Self::Function => BlockType::Function,
            Self::Object => BlockType::Object,
            Self::Unknown => BlockType::Unknown,
            Self::Instance(_) => unreachable!("only typeof kinds are emitted here"),
        }
    }
}
#[derive(Debug, Clone, Copy)]
struct InstanceRecord {
    name: Option<TextId>,
    ancestors: (u32, u32),
}
#[derive(Debug, Clone, Default)]
pub(crate) struct Metadata {
    encoding: crate::types::variant_runtime::LiteralKeyScratch,
    text: String,
    texts: Vec<(u32, u32)>,
    literals: Vec<(Literal, TextId)>,
    instances: Vec<InstanceRecord>,
    ancestors: Vec<TextId>,
    hash: ahash::RandomState,
    text_index: hashbrown::HashTable<TextId>,
    literal_index: hashbrown::HashTable<LiteralId>,
    instance_index: hashbrown::HashTable<InstanceId>,
}
impl Metadata {
    #[cfg(test)]
    pub(crate) fn capacities(&self) -> [usize; 11] {
        [
            self.text.capacity(),
            self.texts.capacity(),
            self.literals.capacity(),
            self.instances.capacity(),
            self.ancestors.capacity(),
            self.text_index.capacity(),
            self.literal_index.capacity(),
            self.instance_index.capacity(),
            self.encoding.capacities()[0],
            self.encoding.capacities()[1],
            self.encoding.capacities()[2],
        ]
    }
    pub(crate) fn text(&self, id: TextId) -> &str {
        let (start, len) = self.texts[id.0 as usize];
        &self.text[start as usize..(start + len) as usize]
    }
    fn intern(&mut self, text: &str) -> TextId {
        let hash = self.hash.hash_one(text);
        if let Some(id) = self.text_index.find(hash, |id| self.text(*id) == text) {
            return *id;
        }
        let id = TextId(self.texts.len() as u32);
        self.texts.push((self.text.len() as u32, text.len() as u32));
        self.text.push_str(text);
        let Self {
            text,
            texts,
            hash: builder,
            text_index,
            ..
        } = self;
        text_index.insert_unique(hash, id, |id| {
            let (start, len) = texts[id.0 as usize];
            builder.hash_one(&text[start as usize..(start + len) as usize])
        });
        id
    }
    pub(crate) fn import_literal(&mut self, tag: &LiteralTag) -> LiteralId {
        let literal = match tag {
            LiteralTag::String(s) => Literal::String(self.intern(s)),
            LiteralTag::Float(s) => Literal::Float(self.intern(s)),
            LiteralTag::BigInt(s) => Literal::BigInt(self.intern(s)),
            LiteralTag::Int(i) => Literal::Int(*i),
            LiteralTag::Bool(b) => Literal::Bool(*b),
            LiteralTag::Null => Literal::Null,
            LiteralTag::Undefined => Literal::Undefined,
        };
        let hash = self.hash.hash_one(literal);
        if let Some(id) = self
            .literal_index
            .find(hash, |id| self.literal(*id) == literal)
        {
            return *id;
        }
        // Runtime equality and structural tag equality are intentionally separate.
        // Canonicalization belongs to import, never to planning/selection.
        let mut encoding = std::mem::take(&mut self.encoding);
        let runtime = self.intern(encoding.encode(tag));
        encoding.output.clear();
        self.encoding = encoding;
        let id = LiteralId(self.literals.len() as u32);
        self.literals.push((literal, runtime));
        let Self {
            literal_index,
            literals,
            hash: builder,
            ..
        } = self;
        literal_index.insert_unique(hash, id, |id| builder.hash_one(literals[id.0 as usize].0));
        id
    }
    pub(crate) fn literal_count(&self) -> usize {
        self.literals.len()
    }
    pub(crate) fn literal(&self, id: LiteralId) -> Literal {
        self.literals[id.0 as usize].0
    }
    pub(crate) fn runtime_key(&self, id: LiteralId) -> &str {
        self.text(self.literals[id.0 as usize].1)
    }
    pub(crate) fn owned_literal(&self, id: LiteralId) -> LiteralTag {
        match self.literal(id) {
            Literal::String(s) => LiteralTag::String(self.text(s).to_owned()),
            Literal::Float(s) => LiteralTag::Float(self.text(s).to_owned()),
            Literal::BigInt(s) => LiteralTag::BigInt(self.text(s).to_owned()),
            Literal::Int(i) => LiteralTag::Int(i),
            Literal::Bool(b) => LiteralTag::Bool(b),
            Literal::Null => LiteralTag::Null,
            Literal::Undefined => LiteralTag::Undefined,
        }
    }
    /// O(1): number of interned immutable instance descriptors.
    pub(crate) fn instance_count(&self) -> usize { self.instances.len() }
    pub(crate) fn instance_name(&self, id: InstanceId) -> &str {
        self.instances[id.0 as usize]
            .name
            .map_or("Array", |name| self.text(name))
    }
    pub(crate) fn is_class(&self, id: InstanceId) -> bool {
        self.instances[id.0 as usize].name.is_some()
    }
    fn ancestors(&self, id: InstanceId) -> &[TextId] {
        let (start, len) = self.instances[id.0 as usize].ancestors;
        &self.ancestors[start as usize..(start + len) as usize]
    }
    pub(crate) fn is_subclass(&self, a: InstanceId, b: InstanceId) -> bool {
        self.instances[b.0 as usize]
            .name
            .is_some_and(|name| self.ancestors(a).contains(&name))
    }
    pub(crate) fn owned_instance(&self, id: InstanceId) -> Instance {
        use crate::types::variant_runtime::{ClassBlocks, ShapeAllocation};
        match self.instances[id.0 as usize].name {
            None => Instance::Array(ShapeAllocation::fresh()),
            Some(name) => Instance::Class {
                name: self.text(name).to_owned(),
                ancestors: self
                    .ancestors(id)
                    .iter()
                    .map(|s| self.text(*s).to_owned())
                    .collect(),
                blocks: ClassBlocks::fresh(0),
            },
        }
    }
    pub(crate) fn import_kind(&mut self, kind: &BlockType) -> Kind {
        match kind {
            BlockType::Number => Kind::Number,
            BlockType::String => Kind::String,
            BlockType::Bigint => Kind::Bigint,
            BlockType::Boolean => Kind::Boolean,
            BlockType::Symbol => Kind::Symbol,
            BlockType::Function => Kind::Function,
            BlockType::Object => Kind::Object,
            BlockType::Unknown => Kind::Unknown,
            BlockType::Instance(instance) => {
                let start = self.ancestors.len();
                let name = match instance {
                    Instance::Array(_) => None,
                    Instance::Class {
                        name, ancestors, ..
                    } => {
                        let name = self.intern(name);
                        for ancestor in ancestors {
                            let id = self.intern(ancestor);
                            self.ancestors.push(id);
                        }
                        Some(name)
                    }
                };
                let hash = self.hash.hash_one((name, &self.ancestors[start..]));
                if let Some(&id) = self.instance_index.find(hash, |id| {
                    self.instances[id.0 as usize].name == name
                        && self.ancestors(*id) == &self.ancestors[start..]
                }) {
                    self.ancestors.truncate(start);
                    return Kind::Instance(id);
                }
                let id = InstanceId(self.instances.len() as u32);
                self.instances.push(InstanceRecord {
                    name,
                    ancestors: (start as u32, (self.ancestors.len() - start) as u32),
                });
                let Self {
                    instance_index,
                    instances,
                    ancestors,
                    hash: builder,
                    ..
                } = self;
                instance_index.insert_unique(hash, id, |id| {
                    let record = instances[id.0 as usize];
                    let (start, len) = record.ancestors;
                    builder.hash_one((
                        record.name,
                        &ancestors[start as usize..(start + len) as usize],
                    ))
                });
                Kind::Instance(id)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_encoding_reuses_buffers_for_ten_thousand_literals() {
        use crate::types::variant_runtime::LiteralKeyScratch;
        let cases = [
            (LiteralTag::Float("0x1.f_8p+3".into()), "number:0x1.f8p+3"),
            (LiteralTag::Float("-0.0".into()), "number:0"),
            (LiteralTag::Float("-NaN".into()), "number:-nan"),
            (LiteralTag::BigInt("-00_123".into()), "bigint:-123"),
            (LiteralTag::BigInt("-000".into()), "bigint:0"),
            (LiteralTag::BigInt("00x1".into()), "bigint:00x1"),
            (LiteralTag::Int(4_294_967_297), "number:0x1p+0"),
            (LiteralTag::String("text".into()), "string:text"),
        ];
        let mut scratch = LiteralKeyScratch::default();
        for (tag, expected) in &cases {
            assert_eq!(scratch.encode(tag), *expected);
        }
        let before = scratch.capacities();
        let measured = allocation_counter::measure(|| {
            for i in 0..10_000 {
                let (tag, expected) = &cases[i % cases.len()];
                assert_eq!(scratch.encode(tag), *expected);
            }
        });
        assert_eq!(measured.count_total, 0, "{measured:?}");
        assert_eq!(scratch.capacities(), before);
    }

    #[test]
    fn handles_preserve_structural_tags_separately_from_runtime_equality() {
        let mut m = Metadata::default();
        let narrow = m.import_literal(&LiteralTag::Int(1));
        let wide = m.import_literal(&LiteralTag::Int(4_294_967_297));
        let float = m.import_literal(&LiteralTag::Float("1.0".into()));
        assert_ne!(narrow, wide);
        assert_ne!(narrow, float);
        assert_eq!(m.literal(wide), Literal::Int(4_294_967_297));
        assert_eq!(m.runtime_key(narrow), m.runtime_key(wide));
        assert_eq!(m.runtime_key(narrow), m.runtime_key(float));
        let bigint = m.import_literal(&LiteralTag::BigInt("+001".into()));
        assert_ne!(m.runtime_key(narrow), m.runtime_key(bigint));
        let first = m.import_kind(&BlockType::Instance(Instance::Array(
            crate::types::ShapeAllocation::fresh(),
        )));
        let second = m.import_kind(&BlockType::Instance(Instance::Array(
            crate::types::ShapeAllocation::fresh(),
        )));
        assert_eq!(first, second);
        let class = || {
            BlockType::Instance(Instance::Class {
                name: "C".into(),
                ancestors: vec!["B".into()],
                blocks: crate::types::ClassBlocks::fresh(1),
            })
        };
        assert_eq!(m.import_kind(&class()), m.import_kind(&class()));
        assert_eq!(std::mem::size_of::<TextId>(), 4);
        assert_eq!(std::mem::size_of::<LiteralId>(), 4);
        assert_eq!(std::mem::size_of::<InstanceId>(), 4);
        assert_eq!(std::mem::size_of::<Literal>(), 16);
        assert_eq!(std::mem::size_of::<Kind>(), 8);
        assert_eq!(std::mem::size_of::<InstanceRecord>(), 16);
        assert_eq!(std::mem::size_of::<super::super::StoredTest>(), 12);
    }
}
