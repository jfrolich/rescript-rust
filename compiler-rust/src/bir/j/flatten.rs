//! Copy-time rules of the legacy statement flattener. Nested lists are already copied.
use super::{norm, plain as p};
use crate::bir::{Bir, NodeId, View};
use crate::js_ir::BinOp;

#[derive(Clone, Copy)]
enum End { Effect, Return, Assign(NodeId) }
#[derive(Clone, Copy)]
enum Work {
    Statement(NodeId),
    Operand(NodeId, End),
    Block(u32),
    Conditional(NodeId, NodeId, u8),
}

/// Reused by the owner of the statement run; no scratch allocation per statement.
#[derive(Default)]
pub(crate) struct Flatten {
    work: Vec<Work>,
    values: Vec<NodeId>,
    pub(crate) steps: usize,
}

impl Flatten {
    /// R1–R8. Linear: one step per statement written plus one per operand
    /// of a flattened sequence (and its binary spine). Scratch grows only to
    /// the maximum pending depth/run, never once per statement. Nested lists
    /// are not revisited. The caller owns both scratch buffers across calls.
    pub(crate) fn flatten_into(&mut self, b: &mut Bir, statement: NodeId, out: &mut Vec<NodeId>) {
        debug_assert!(self.work.is_empty() && self.values.is_empty());
        self.work.push(Work::Statement(statement));
        while let Some(work) = self.work.pop() {
            match work {
                Work::Statement(s) => {
                    self.steps += 1;
                    match b.view(s) {
                        View::SBlock { statements: [inner] } => {
                            let inner = *inner;
                            p::retain(b, &[s], &[inner]);
                            self.work.push(Work::Statement(inner));
                        }
                        View::SExp { value } | View::SReturn { value } => {
                            let returning = matches!(b.view(s), View::SReturn { .. });
                            let end = if returning { End::Return } else { End::Effect };
                            match b.view(value) {
                                View::JSeq { .. } => {
                                    p::retain(b, &[s], &[value]);
                                    self.work.push(Work::Block(self.values.len() as u32));
                                    self.work.push(Work::Operand(value, end));
                                }
                                View::JBlockLit { values, .. } if !returning => {
                                    let count = values.len();
                                    self.work.push(Work::Block(self.values.len() as u32));
                                    for i in (0..count).rev() {
                                        let View::JBlockLit { values, .. } = b.view(value) else { unreachable!() };
                                        let child = values[i];
                                        b.detach(child);
                                        self.work.push(Work::Operand(child, End::Effect));
                                    }
                                    b.release(s);
                                }
                                View::JCond { then_, else_, .. } => {
                                    let yes = returning || !p::pure(b, then_);
                                    let no = returning || !p::pure(b, else_);
                                    self.work.push(Work::Conditional(s, value, u8::from(yes) | (u8::from(no) << 1)));
                                    if no { b.detach(else_); self.work.push(Work::Operand(else_, end)); }
                                    if yes { b.detach(then_); self.work.push(Work::Operand(then_, end)); }
                                }
                                View::JBin { left, right } if !returning && b.node(value).aux() == BinOp::Eq as u16 && matches!(b.view(right), View::JSeq { .. }) => {
                                    p::retain(b, &[s], &[left, right]);
                                    self.work.push(Work::Block(self.values.len() as u32));
                                    self.work.push(Work::Operand(right, End::Assign(left)));
                                }
                                _ => self.values.push(s),
                            }
                        }
                        _ => self.values.push(s),
                    }
                }
                Work::Operand(value, end) => {
                    if let View::JSeq { first, second } = b.view(value) {
                        p::retain(b, &[value], &[first, second]);
                        self.work.push(Work::Operand(second, end));
                        self.work.push(Work::Operand(first, End::Effect));
                    } else {
                        let statement = match end {
                            End::Effect => norm::js1_exp(b, value),
                            End::Return => p::node(b, View::SReturn { value }, 0),
                            End::Assign(left) => {
                                let value = p::bin(b, BinOp::Eq, left, value);
                                norm::js1_exp(b, value)
                            }
                        };
                        self.work.push(Work::Statement(statement));
                    }
                }
                Work::Block(start) => {
                    // J-S2/J-S5 without transferring ownership of the reusable Vec.
                    let start = start as usize;
                    let result = if self.values.len() == start + 1 {
                        self.values[start]
                    } else {
                        let list = b.lists.push(&self.values[start..]);
                        b.explicit_block_from_list(list)
                    };
                    self.values.truncate(start);
                    self.values.push(result);
                }
                Work::Conditional(s, value, mask) => {
                    let no = if mask & 2 != 0 { self.values.pop() } else { None };
                    let yes = if mask & 1 != 0 { self.values.pop() } else { None };
                    let View::JCond { condition, .. } = b.view(value) else { unreachable!() };
                    b.detach(condition);
                    let result = match (yes, no) {
                        (None, None) => if p::pure(b, condition) {
                            b.release(condition);
                            p::node(b, View::SBlock { statements: &[] }, 1)
                        } else { p::node(b, View::SExp { value: condition }, 0) },
                        (yes, no) => {
                            let (condition, yes, no) = if yes.is_none() {
                                (norm::je8_not(b, condition), no, None)
                            } else { (condition, yes, no) };
                            let then_ = p::list(b, yes.as_slice());
                            let else_ = p::list(b, no.as_slice());
                            p::node(b, View::SIf { condition, then_, else_: Some(else_) }, 0)
                        }
                    };
                    p::copy_cold(b, value, result);
                    let comment = b.cold(s).and_then(|c| c.comment);
                    if let Some(mut cold) = b.cold(result) { cold.comment = comment; b.set_cold(result, cold); }
                    b.release(s);
                    self.values.push(result);
                }
            }
        }
        let result = self.values.pop().expect("flatten result");
        debug_assert!(self.values.is_empty());
        if let View::SBlock { statements } = b.view(result) {
            let count = statements.len();
            for i in 0..count {
                let View::SBlock { statements } = b.view(result) else { unreachable!() };
                let s = statements[i];
                b.detach(s);
                out.push(s);
            }
            b.release(result);
        } else { out.push(result); }
    }
}

#[cfg(test)]
mod sizes {
    use super::*;
    #[test]
    fn work_entry_size() {
        assert_eq!(std::mem::size_of::<Work>(), 16);
        assert_eq!(std::mem::size_of::<End>(), 8);
        assert_eq!(std::mem::size_of::<Flatten>(), 56);
    }
}
