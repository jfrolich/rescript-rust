//! The canonical text of a unit's exported signature, printed from its
//! [`Segment`]. The text is byte for byte the one types/canonical_sig.rs
//! `canonical_signature` prints for the same unit from the old checker's
//! graph (docs/CHECKER_REWRITE.md, R2); this module derives it from the
//! segment's typed pools alone, through no other representation.
//!
//! The text has three parts:
//!
//! 1. `unit <name>` and, when the unit is deprecated, `deprecated "<why>"`;
//! 2. `== printed`: the signature as `Printtyp` prints it for a user,
//!    through the outcome printer at width 80 (`printed`);
//! 3. `== items`: per item, what the printer leaves out (`items`): every
//!    type by structure with shared nodes numbered, runtime
//!    representations, variance, primitives and attributes.
//!
//! The old printer changes the graph while it prints the first section
//! (row and object normalization, the name of a `_` parameter), and the
//! second section reads the changed graph; `view::Graph` keeps those
//! changes as an overlay, so the segment stays immutable.
//!
//! Identity. A node is one handle of the segment: generic nodes of an item
//! are its template's, shared positions stay one node and equal nodes stay
//! two; non-generic nodes are the segment's shared nodes. Identifiers are
//! compared as `Ident.same` compares them (equal nonzero stamps, or equal
//! names when persistent); no stamp is ever printed.
//!
//! Cost. Dense-index construction sorts identifiers once. Printing visits
//! metadata and type nodes, re-expanding sharing where the old printer does.
//! Object/variant fields are sorted; variant conjunctions additionally use
//! structural equality (its comparison costs are documented in normalize.rs). Every walk (types,
//! loop marks, normalization, documents, signatures, module types, paths)
//! runs on an explicit stack; per-node state is in dense tables.

mod doc;
mod items;
mod normalize;
mod printed;
mod text;
mod view;

use std::fmt::Write as _;

use crate::tc::segment::Segment;

/// The canonical text of the unit `segment` publishes (see the module
/// documentation). Panics on a segment without a unit row.
pub fn canonical_signature(segment: &Segment) -> String {
    let unit = segment
        .signature
        .unit
        .expect("a unit's segment has a unit row");
    let mut graph = view::Graph::new(view::View::new(segment));
    let mut out = String::new();
    let _ = writeln!(out, "unit {}", graph.v.str(unit.name));
    if let Some(reason) = graph.v.opt_str(unit.deprecated) {
        let _ = writeln!(out, "deprecated {reason:?}");
    }
    out.push_str("== printed\n");
    let printed = printed::Printed::new(&mut graph).run(unit.signature);
    out.push_str(&printed);
    out.push_str("\n== items\n");
    items::Items::new(&mut graph, out).run(unit.signature)
}

#[cfg(test)]
mod tests {
    use super::canonical_signature;
    use crate::tc::graph::{ARROW, GENERIC, NONE, Node, Param, TUPLE, Ty, VAR};
    use crate::tc::segment::*;

    /// A segment built row by row: shared nodes only, one value per item.
    #[derive(Default)]
    struct Builder {
        segment: Segment,
        bytes: Vec<u8>,
        strings: Vec<Range>,
        nodes: Vec<Node>,
        lists: Vec<Ty>,
        params: Vec<Param>,
        identifiers: Vec<IdentRow>,
        items: Vec<SignatureItemRow>,
        values: Vec<ValueRow>,
        roots: Vec<SchemeRoot>,
    }

    impl Builder {
        fn string(&mut self, text: &str) -> u32 {
            let start = self.bytes.len() as u32;
            self.bytes.extend_from_slice(text.as_bytes());
            self.strings.push(Range {
                start,
                len: text.len() as u32,
            });
            self.strings.len() as u32 - 1
        }

        fn node(&mut self, node: Node) -> u32 {
            self.nodes.push(node);
            self.nodes.len() as u32 - 1
        }

        fn var(&mut self, level: u32) -> u32 {
            self.node(Node {
                head: VAR,
                level,
                a: NONE,
                b: 0,
            })
        }

        fn arrow(&mut self, arg: u32, ret: u32) -> u32 {
            let b = self.params.len() as u32;
            self.params.push(Param {
                ty: Ty(arg),
                label: NONE,
                loc: NONE,
            });
            self.node(Node {
                head: ARROW | 1 << 8,
                level: GENERIC,
                a: ret,
                b,
            })
        }

        fn tuple(&mut self, children: &[u32]) -> u32 {
            let b = self.lists.len() as u32;
            self.lists.extend(children.iter().map(|&child| Ty(child)));
            self.node(Node {
                head: TUPLE | (children.len() as u32) << 8,
                level: GENERIC,
                a: 0,
                b,
            })
        }

        fn value(&mut self, name: &str, ty: u32) {
            let name = self.string(name);
            self.identifiers.push(IdentRow {
                name,
                stamp: self.identifiers.len() as i32 + 1,
                flags: 0,
                scope: self.items.len() as u32,
            });
            let ident = self.identifiers.len() as u32 - 1;
            self.roots.push(SchemeRoot {
                template: NONE,
                ty: Ty(ty),
            });
            self.values.push(ValueRow {
                ty: self.roots.len() as u32 - 1,
                primitive: NONE,
                attributes: Range::default(),
                loc: NONE,
                path: NONE,
            });
            self.items.push(SignatureItemRow {
                ident,
                declaration: self.values.len() as u32 - 1,
                kind: SignatureKind::Value,
                status: ItemStatus::Ordinary,
            });
        }

        fn finish(mut self, unit: &str) -> Segment {
            let name = self.string(unit);
            let items = self.items.len() as u32;
            self.segment.nodes = self.nodes.into_boxed_slice();
            self.segment.lists = self.lists.into_boxed_slice();
            self.segment.params = self.params.into_boxed_slice();
            let pools = &mut self.segment.signature;
            pools.unit = Some(UnitRow {
                name,
                deprecated: NONE,
                signature: 0,
                path: NONE,
            });
            pools.bytes = self.bytes.into_boxed_slice();
            pools.strings = self.strings.into_boxed_slice();
            pools.identifiers = self.identifiers.into_boxed_slice();
            pools.ordered_items = self.items.into_boxed_slice();
            pools.signatures = Box::new([Range {
                start: 0,
                len: items,
            }]);
            pools.values = self.values.into_boxed_slice();
            pools.roots = self.roots.into_boxed_slice();
            self.segment
        }
    }

    #[test]
    fn unresolved_package_components_keep_both_canonical_spellings() {
        let mut b = Builder::default();
        let name = b.string("S");
        b.identifiers.push(IdentRow {
            name,
            stamp: 33,
            flags: 0,
            scope: NONE,
        });
        b.segment.signature.paths = Box::new([PathRow::Ident(0)]);
        b.segment.signature.longidents = Box::new([
            LongidentRow::Unresolved(7),
            LongidentRow::UnresolvedDot { parent: 0, raw: 9 },
            LongidentRow::Unresolved(7),
            LongidentRow::UnresolvedDot { parent: 2, raw: 9 },
        ]);
        b.segment.signature.indices = Box::new([1, 3]);
        b.segment.signature.packages = Box::new([PackageRow {
            path: 0,
            longidents: Range { start: 0, len: 1 },
            arguments: Range { start: 0, len: 1 },
        }]);
        b.segment.signature.descriptor_extras = Box::new([ExtraDescriptor::Package(0)]);
        let arg = b.var(GENERIC);
        b.lists.push(Ty(arg));
        let package = b.node(Node {
            head: TUPLE | EXTENDED | (1 << 8),
            level: GENERIC,
            a: 0,
            b: 0,
        });
        let first = b.segment.signature.packages[0];
        b.segment.signature.packages = Box::new([
            first,
            PackageRow {
                longidents: Range { start: 1, len: 1 },
                ..first
            },
        ]);
        b.segment.signature.descriptor_extras =
            Box::new([ExtraDescriptor::Package(0), ExtraDescriptor::Package(1)]);
        let same = b.node(Node {
            head: TUPLE | EXTENDED | (1 << 8),
            level: GENERIC,
            a: 1,
            b: 0,
        });
        b.value("packed", package);
        let segment = b.finish("Unresolved");
        let mut graph = super::view::Graph::new(super::view::View::new(&segment));
        assert!(graph.equal(super::view::N(package), super::view::N(same)));
        let text = canonical_signature(&segment);
        let (printed, items) = text.split_once("== items\n").unwrap();
        assert!(printed.contains("with type #7.#9 = 'a"), "{printed}");
        assert!(
            items.contains("with <unresolved>.<unresolved> = '0"),
            "{items}"
        );
    }

    #[test]
    fn polymorphic_body_and_variable_slots_have_different_offsets() {
        let mut b = Builder::default();
        let a = b.var(GENERIC);
        let body = b.arrow(a, a);
        b.segment.signature.descriptor_extras = Box::new([ExtraDescriptor::Poly]);
        let mut polys = Vec::new();
        for variables in [0, 1] {
            let start = b.lists.len() as u32;
            b.lists.push(Ty(body));
            if variables == 1 {
                b.lists.push(Ty(a));
            }
            polys.push(b.node(Node {
                head: TUPLE | EXTENDED | ((variables + 1) << 8),
                level: GENERIC,
                a: 0,
                b: start,
            }));
        }
        let segment = b.finish("PolySlots");
        let graph = super::view::Graph::new(super::view::View::new(&segment));
        for (variables, poly) in polys.into_iter().enumerate() {
            let super::view::Desc::Poly { body: actual, vars } = graph.desc(super::view::N(poly))
            else {
                panic!("expected a polymorphic descriptor");
            };
            assert_eq!(actual, super::view::N(body));
            assert_eq!(vars.len as usize, variables);
            if variables == 1 {
                assert_eq!(graph.slot(vars, 0), super::view::N(a));
            }
        }
    }

    #[test]
    fn equality_walks_ten_thousand_nodes_without_recursion() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut b = Builder::default();
                let var = b.var(GENERIC);
                let (mut left, mut right) = (var, var);
                for _ in 0..10_000 {
                    left = b.tuple(&[left]);
                    right = b.tuple(&[right]);
                }
                let segment = b.finish("Equal");
                let mut graph = super::view::Graph::new(super::view::View::new(&segment));
                assert!(graph.equal(super::view::N(left), super::view::N(right)));
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn a_polymorphic_identity_prints_both_sections() {
        let mut b = Builder::default();
        let a = b.var(GENERIC);
        let id = b.arrow(a, a);
        b.value("id", id);
        let weak = b.var(3);
        b.value("cell", weak);
        let other = b.var(GENERIC);
        let pair = b.tuple(&[a, a, other]);
        b.value("dup", pair);
        let text = canonical_signature(&b.finish("Test"));
        assert_eq!(
            text,
            "unit Test\n== printed\n{\n  let id: 'a => 'a\n  let cell: '_weak1\n  let dup: ('a, 'a, 'b)\n}\n\
             == items\nvalue id: &0(('0) => '0)\nvalue cell: '_0\nvalue dup: &0(tuple('0, '0, '1))\n"
        );
    }

    #[test]
    fn ten_thousand_deep_arrows_and_wide_tuples_on_a_two_mb_stack() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut b = Builder::default();
                let a = b.var(GENERIC);
                let mut ty = a;
                for _ in 0..10000 {
                    ty = b.arrow(a, ty);
                }
                b.value("deep", ty);
                let children = vec![a; 10000];
                let wide = b.tuple(&children);
                b.value("wide", wide);
                let segment = b.finish("Test");
                let mut text = String::new();
                let steps = crate::tc::steps::scope(|| text = canonical_signature(&segment));
                assert_eq!(text.matches(" => ").count(), 2 * 10000);
                assert!(text.contains("value deep: &0(('0) => &1(('0) => "));
                assert_eq!(text.matches("'0").count(), 10001 + 10000);
                // Each node is entered a bounded number of times per section.
                assert!(steps <= 20 * 20002, "{steps}");
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn modules_aliases_module_types_and_functors() {
        let mut b = Builder::default();
        let a = b.var(GENERIC);
        b.value("x", a);
        let unit = b.string("Mods");
        b.identifiers.push(IdentRow {
            name: unit,
            stamp: 0,
            flags: 0,
            scope: UNIT_SCOPE,
        });
        let unit_ident = b.identifiers.len() as u32 - 1;
        let ident = |b: &mut Builder, name: &str, scope: u32| {
            let name = b.string(name);
            b.identifiers.push(IdentRow {
                name,
                stamp: 100 + b.identifiers.len() as i32,
                flags: 0,
                scope,
            });
            b.identifiers.len() as u32 - 1
        };
        let m = ident(&mut b, "M", 1);
        let alias = ident(&mut b, "Alias", 2);
        let s = ident(&mut b, "S", 3);
        let f = ident(&mut b, "F", 4);
        let p = ident(&mut b, "P", FUNCTOR_SCOPE | 3);
        let name_m = b.identifiers[m as usize].name;
        let modules = [
            (m, 0, SignatureKind::Module),
            (alias, 1, SignatureKind::Module),
            (s, NONE, SignatureKind::ModuleType),
            (f, 3, SignatureKind::Module),
        ];
        let mut rows = Vec::new();
        for (ident, module_type, kind) in modules {
            rows.push(ModuleRow {
                module_type,
                attributes: Range::default(),
                loc: NONE,
                path: NONE,
            });
            b.items.push(SignatureItemRow {
                ident,
                declaration: rows.len() as u32 - 1,
                kind,
                status: if kind == SignatureKind::Module {
                    ItemStatus::Recursive(RecStatus::Not)
                } else {
                    ItemStatus::Ordinary
                },
            });
        }
        let mut segment = b.finish("Mods");
        let pools = &mut segment.signature;
        pools.unit = Some(UnitRow {
            name: unit,
            deprecated: NONE,
            signature: 0,
            path: NONE,
        });
        pools.signatures = Box::new([
            Range { start: 1, len: 4 },
            Range { start: 0, len: 1 },
            Range { start: 5, len: 0 },
        ]);
        pools.paths = Box::new([
            PathRow::Ident(unit_ident),
            PathRow::Dot {
                parent: 0,
                name: name_m,
                position: 1,
            },
        ]);
        pools.module_types = Box::new([
            ModuleTypeRow::Signature(1),
            ModuleTypeRow::Alias {
                path: 1,
                present: false,
            },
            ModuleTypeRow::Signature(2),
            ModuleTypeRow::Functor {
                parameter: p,
                parameter_type: NONE,
                result: 2,
            },
        ]);
        pools.modules = rows.into_boxed_slice();
        assert_eq!(
            canonical_signature(&segment),
            "unit Mods\n== printed\n{\n  module M: {\n    let x: 'a\n  }\n  module Alias = M\n  \
             module type S =\n  module F: () =>\n}\n== items\nmodule M TrecNot\n  sig\n    \
             value x: '0\nmodule Alias TrecNot\n  alias MtaAbsent M\nmodtype S\n  abstract\n\
             module F TrecNot\n  functor P\n    generative\n    result\n    sig\n"
        );
    }

    #[test]
    fn ten_thousand_items_number_each_item_afresh() {
        let mut b = Builder::default();
        let shared = b.var(2);
        for i in 0..10000 {
            let pair = b.tuple(&[shared, shared]);
            b.value(&format!("v{i}"), pair);
        }
        let text = canonical_signature(&b.finish("Wide"));
        assert_eq!(text.matches("&0(tuple('_0, '_0))").count(), 10000);
        assert_eq!(text.matches("('_weak1, '_weak1)").count(), 10000);
    }
}
