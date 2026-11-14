//! Immutable spelling and runtime-equality metadata, populated before planning.
use crate::types::variant_runtime::{BlockType, Instance, LiteralTag};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TextId(u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct LiteralId(pub(crate) u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InstanceId(pub(crate) u32);
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Literal {
    String(TextId),
    Int(i64),
    Float(TextId),
    BigInt(TextId),
    Bool(bool),
    Null,
    Undefined,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    /// Cost: O(1); reads a scalar or borrowed pool range.
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
    /// Cost: O(1); reads a scalar or borrowed pool range.
    #[cfg(test)]
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
const NONE: u32 = u32::MAX;

/// Dense AVL links: row i indexes metadata row i, without per-entry allocation.
#[derive(Debug, Clone, Copy)]
struct Links {
    children: [u32; 2],
    parent: u32,
    height: u32,
}
#[derive(Debug, Clone)]
struct Index {
    nodes: Vec<Links>,
    root: u32,
    #[cfg(test)]
    steps: std::cell::Cell<usize>,
}
impl Default for Index {
    /// Cost: O(1), initializing an empty link pool without allocating.
    fn default() -> Self {
        Self { nodes: Vec::new(), root: NONE, #[cfg(test)] steps: std::cell::Cell::new(0) }
    }
}
impl Index {
    #[cfg(test)]
    /// Cost: O(1), reading the link pool capacity.
    fn capacity(&self) -> usize { self.nodes.capacity() }
    /// Cost: O(existing rows) if relocation is needed; reserves space for n links.
    fn reserve_exact(&mut self, n: usize) { self.nodes.reserve_exact(n); }
    /// Cost: O(log U) key comparisons, where U is the number of indexed rows.
    fn find(&self, mut compare: impl FnMut(u32) -> std::cmp::Ordering) -> Result<u32, (u32, usize)> {
        let (mut node, mut parent, mut side) = (self.root, NONE, 0);
        while node != NONE {
            #[cfg(test)]
            self.steps.set(self.steps.get() + 1);
            side = match compare(node) {
                std::cmp::Ordering::Equal => return Ok(node),
                std::cmp::Ordering::Less => 1,
                std::cmp::Ordering::Greater => 0,
            };
            parent = node;
            node = self.nodes[node as usize].children[side];
        }
        Err((parent, side))
    }
    /// Cost: O(1), reading one stored height (zero for an absent child).
    fn height(&self, node: u32) -> u32 {
        if node == NONE { 0 } else { self.nodes[node as usize].height }
    }
    /// Cost: O(1), comparing two child heights and updating one link row.
    fn refresh(&mut self, node: u32) {
        let [left, right] = self.nodes[node as usize].children;
        self.nodes[node as usize].height = 1 + self.height(left).max(self.height(right));
        #[cfg(test)]
        self.steps.set(self.steps.get() + 2); // height comparison and field move
    }
    /// Cost: O(1), relinking at most four rows and refreshing two heights.
    fn rotate(&mut self, node: u32, side: usize) -> u32 {
        let parent = self.nodes[node as usize].parent;
        let pivot = self.nodes[node as usize].children[side];
        let middle = self.nodes[pivot as usize].children[1 - side];
        self.nodes[node as usize].children[side] = middle;
        if middle != NONE { self.nodes[middle as usize].parent = node; }
        self.nodes[pivot as usize].children[1 - side] = node;
        self.nodes[node as usize].parent = pivot;
        self.nodes[pivot as usize].parent = parent;
        if parent == NONE { self.root = pivot; }
        else {
            let child = usize::from(self.nodes[parent as usize].children[1] == node);
            self.nodes[parent as usize].children[child] = pivot;
        }
        #[cfg(test)]
        self.steps.set(self.steps.get() + 12); // upper bound on row-field moves/comparisons
        self.refresh(node);
        self.refresh(pivot);
        pivot
    }
    /// Cost: O(log U) link/height updates and at most two rotations, plus one
    /// amortized O(1) row append (O(U) if its backing pool must relocate).
    /// Appends preserve dense metadata handles, with no sorted-vector shifts.
    fn insert(&mut self, (parent, side): (u32, usize), id: u32) {
        assert_eq!(id as usize, self.nodes.len());
        self.nodes.push(Links { children: [NONE; 2], parent, height: 1 });
        if parent == NONE { self.root = id; }
        else { self.nodes[parent as usize].children[side] = id; }
        #[cfg(test)]
        self.steps.set(self.steps.get() + 2);
        let mut node = parent;
        while node != NONE {
            let old_height = self.nodes[node as usize].height;
            #[cfg(test)]
            self.steps.set(self.steps.get() + 4); // balance tests and height-stop comparison
            self.refresh(node);
            let [left, right] = self.nodes[node as usize].children;
            let balance = self.height(left) as i64 - self.height(right) as i64;
            if balance > 1 {
                let [ll, lr] = self.nodes[left as usize].children;
                if self.height(ll) < self.height(lr) { self.rotate(left, 1); }
                node = self.rotate(node, 0);
            } else if balance < -1 {
                let [rl, rr] = self.nodes[right as usize].children;
                if self.height(rl) > self.height(rr) { self.rotate(right, 0); }
                node = self.rotate(node, 1);
            }
            if self.nodes[node as usize].height == old_height { break; }
            node = self.nodes[node as usize].parent;
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Metadata {
    encoding: crate::types::variant_runtime::LiteralKeyScratch,
    text: String,
    texts: Vec<(u32, u32)>,
    literals: Vec<(Literal, TextId)>,
    instances: Vec<InstanceRecord>,
    ancestors: Vec<TextId>,
    text_index: Index,
    literal_index: Index,
    instance_index: Index,
}
impl Metadata {
    /// Cost: O(K + A) length reads for K kind descriptors and A ancestor names;
    /// reserves their B spelling bytes and the instance/ancestry rows.
    pub(crate) fn reserve_kinds<'a>(&mut self, kinds: impl Iterator<Item = &'a BlockType>) {
        let (mut instances, mut names, mut bytes, mut ancestors) = (0, 0, 0, 0);
        for kind in kinds {
            if let BlockType::Instance(instance) = kind {
                instances += 1;
                if let Instance::Class { name, ancestors: parents, .. } = instance {
                    names += 1 + parents.len();
                    bytes += name.len() + parents.iter().map(String::len).sum::<usize>();
                    ancestors += parents.len();
                }
            }
        }
        let text_rows = self.texts.capacity() + names;
        self.text.reserve_exact(self.text.capacity() + bytes - self.text.len());
        self.texts.reserve_exact(text_rows - self.texts.len());
        self.text_index.reserve_exact(text_rows - self.text_index.nodes.len());
        self.instances.reserve_exact(instances);
        self.instance_index.reserve_exact(instances);
        self.ancestors.reserve_exact(ancestors);
    }

    /// Cost: O(L) tag/length reads for L source literals; reserves B source and
    /// canonical spelling bytes plus dense index rows, without interning. Float
    /// hex keys fit in forty bytes; existing pool relocation adds its row/byte cost.
    pub(crate) fn reserve_literals<'a>(&mut self, tags: impl Iterator<Item = &'a LiteralTag>) {
        let (mut count, mut bytes, mut encoding) = (0, 0, 0);
        for tag in tags {
            let (source, key) = match tag {
                LiteralTag::String(s) => (s.len(), s.len() + 7),
                LiteralTag::BigInt(s) => (s.len(), s.len() + 8),
                LiteralTag::Float(s) => (s.len(), (s.len() + 7).max(40)),
                LiteralTag::Int(_) => (0, 40),
                LiteralTag::Bool(_) => (0, 5),
                LiteralTag::Null => (0, 4),
                LiteralTag::Undefined => (0, 9),
            };
            count += 1;
            bytes += source + key;
            encoding = encoding.max(key);
        }
        self.text.reserve_exact(bytes);
        self.texts.reserve_exact(2 * count);
        self.text_index.reserve_exact(2 * count);
        self.literals.reserve_exact(count);
        self.literal_index.reserve_exact(count);
        self.encoding.output.reserve_exact(encoding);
    }

    #[cfg(test)]
    /// Cost: O(1); reads a scalar or borrowed pool range.
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
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn text(&self, id: TextId) -> &str {
        let (start, len) = self.texts[id.0 as usize];
        &self.text[start as usize..(start + len) as usize]
    }
    /// Cost: O(B log U) key comparisons plus O(B) copied bytes for a new string,
    /// and O(log U) AVL link updates; B is spelling length, U unique strings.
    fn intern(&mut self, text: &str) -> TextId {
        let slot = match self.text_index.find(|id| self.text(TextId(id)).cmp(text)) {
            Ok(id) => return TextId(id),
            Err(slot) => slot,
        };
        let id = TextId(self.texts.len() as u32);
        self.texts.push((self.text.len() as u32, text.len() as u32));
        self.text.push_str(text);
        self.text_index.insert(slot, id.0);
        id
    }
    /// Cost: O(B log U + log L) comparisons/link updates and O(B) encoding,
    /// for B spelling bytes, U unique strings and L unique literals. No shifts.
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
        let slot = match self.literal_index.find(|id| self.literal(LiteralId(id)).cmp(&literal)) {
            Ok(id) => return LiteralId(id),
            Err(slot) => slot,
        };
        // Runtime equality and structural tag equality are intentionally separate.
        // Canonicalization belongs to import, never to planning/selection.
        let mut encoding = std::mem::take(&mut self.encoding);
        let runtime = self.intern(encoding.encode(tag));
        encoding.output.clear();
        self.encoding = encoding;
        let id = LiteralId(self.literals.len() as u32);
        self.literals.push((literal, runtime));
        self.literal_index.insert(slot, id.0);
        id
    }
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn literal_count(&self) -> usize {
        self.literals.len()
    }
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn literal(&self, id: LiteralId) -> Literal {
        self.literals[id.0 as usize].0
    }
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn runtime_key(&self, id: LiteralId) -> &str {
        self.text(self.literals[id.0 as usize].1)
    }
    #[cfg(test)]
    /// Cost: O(literal spelling bytes), for test projection only.
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
    #[cfg(test)]
    /// O(1): number of interned immutable instance descriptors.
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn instance_count(&self) -> usize { self.instances.len() }
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn instance_name(&self, id: InstanceId) -> &str {
        self.instances[id.0 as usize]
            .name
            .map_or("Array", |name| self.text(name))
    }
    /// Cost: O(1); reads a scalar or borrowed pool range.
    pub(crate) fn is_class(&self, id: InstanceId) -> bool {
        self.instances[id.0 as usize].name.is_some()
    }
    /// Cost: O(1); reads a scalar or borrowed pool range.
    fn ancestors(&self, id: InstanceId) -> &[TextId] {
        let (start, len) = self.instances[id.0 as usize].ancestors;
        &self.ancestors[start as usize..(start + len) as usize]
    }
    /// Cost: O(ancestor count); reads immutable interned handles.
    pub(crate) fn is_subclass(&self, a: InstanceId, b: InstanceId) -> bool {
        self.instances[b.0 as usize]
            .name
            .is_some_and(|name| self.ancestors(a).contains(&name))
    }
    /// Cost: O(B log U + A log I) comparisons and O(A + log I) row/link updates,
    /// for B total name bytes, A ancestors, U strings and I unique instances.
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
                let slot = match self.instance_index.find(|id| {
                    self.instances[id as usize].name.cmp(&name)
                        .then_with(|| self.ancestors(InstanceId(id)).cmp(&self.ancestors[start..]))
                }) {
                    Ok(id) => {
                        self.ancestors.truncate(start);
                        return Kind::Instance(InstanceId(id));
                    }
                    Err(slot) => slot,
                };
                let id = InstanceId(self.instances.len() as u32);
                self.instances.push(InstanceRecord {
                    name,
                    ancestors: (start as u32, (self.ancestors.len() - start) as u32),
                });
                self.instance_index.insert(slot, id.0);
                Kind::Instance(id)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reverse_order_interning_has_n_log_n_index_work() {
        let n = 10_000usize;
        let tags: Vec<_> = (0..n).rev().map(|i| LiteralTag::String(format!("literal-{i:05}"))).collect();
        let mut metadata = Metadata::default();
        metadata.reserve_literals(tags.iter());
        let mut ids = Vec::with_capacity(n);
        for tag in &tags { ids.push(metadata.import_literal(tag)); }
        let steps = metadata.text_index.steps.get() + metadata.literal_index.steps.get();
        let limit = (20.0 * n as f64 * (n as f64).log2()) as usize;
        assert!(steps <= limit, "index steps={steps}, limit={limit}");
        for (tag, &id) in tags.iter().zip(&ids) {
            assert_eq!(metadata.import_literal(tag), id);
            assert_eq!(metadata.owned_literal(id), *tag);
        }
        fn check(index: &Index, node: u32, parent: u32) -> u32 {
            if node == NONE { return 0; }
            let row = index.nodes[node as usize];
            assert_eq!(row.parent, parent);
            let left = check(index, row.children[0], node);
            let right = check(index, row.children[1], node);
            assert!(left.abs_diff(right) <= 1);
            assert_eq!(row.height, 1 + left.max(right));
            row.height
        }
        check(&metadata.text_index, metadata.text_index.root, NONE);
        check(&metadata.literal_index, metadata.literal_index.root, NONE);
        println!("reverse literal interning: literals={n}; index moves/comparisons<={steps}; limit={limit}");
    }

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
