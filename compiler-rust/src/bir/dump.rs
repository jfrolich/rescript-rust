//! Stable text for debugging, independent of hash iteration order.
use super::*;
use std::fmt::Write;

impl Bir {
    /// Dump pool IDs and operands in slot order, including detached live trees.
    /// Freed slots are omitted; names and text are escaped using Rust Debug.
    pub fn dump(&self) -> String {
        let mut out = String::new();
        for i in 0..self.vars.len() {
            let v = VarId(index(i));
            writeln!(
                out,
                "v{i} {:?} order={} uses={} flags={:02x} binder={:?} fact={:?}",
                self.vars.name(v).as_str(),
                self.vars.order(v),
                self.vars.uses(v),
                self.vars.flags(v).0,
                self.vars.binder(v),
                self.vars.fact(v)
            )
            .unwrap();
        }
        for (i, node) in self.nodes.iter().enumerate() {
            if node.op() == Op::Free {
                continue;
            }
            writeln!(
                out,
                "n{i} {:?} aux={} flags={:02x}",
                node.view(&self.lists),
                node.aux(),
                node.flags().0
            )
            .unwrap();
        }
        for (i, value) in self.pools.consts.iter().enumerate() {
            writeln!(out, "const{i} {value:?}").unwrap();
        }
        for i in 0..self.pools.strings.len() {
            writeln!(out, "str{i} {:?}", self.text(StrId(index(i)))).unwrap();
        }
        for (i, value) in self.pools.prims.iter().enumerate() {
            writeln!(out, "prim{i} {value:?}").unwrap();
        }
        for (i, value) in self.vars.funcs.iter().enumerate() {
            writeln!(
                out,
                "func{i} {value:?} {:?}",
                self.pools.attrs[value.attr as usize]
            )
            .unwrap();
        }
        for (i, value) in self.pools.switches.iter().enumerate() {
            writeln!(out, "switch{i} {value:?}").unwrap();
        }
        for (i, value) in self.pools.catches.iter().enumerate() {
            writeln!(out, "catch{i} {value:?}").unwrap();
        }
        for (i, value) in self.pools.imports.iter().enumerate() {
            writeln!(out, "import{i} {value:?}").unwrap();
        }
        for (i, value) in self.pools.apply.iter().enumerate() {
            writeln!(out, "apply{i} {value:?}").unwrap();
        }
        for (i, value) in self.pools.js.iter().enumerate() {
            writeln!(out, "js{i} {value:?}").unwrap();
        }
        for (i, value) in self.pools.const_fields.iter().enumerate() {
            writeln!(out, "field{i} {value:?}").unwrap();
        }
        for (i, value) in self.cold.iter().enumerate() {
            if let Some(value) = value {
                writeln!(out, "cold n{i} {:?}", self.pools.cold[value.index()]).unwrap();
            }
        }
        for &(var, name) in &self.exports {
            writeln!(out, "export {var:?} {:?}", name.as_str()).unwrap();
        }
        out
    }
}
