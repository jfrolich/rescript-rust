//! Documents in one arena, laid out as compiler-rust/src/parser/doc.rs lays
//! out `Res_doc` documents (`propagate_forced_breaks`, `fits`, `to_string`
//! at width 80), for the constructs the outcome printer uses. Nodes are
//! built bottom-up, so a child's handle is below its parent's: forced
//! breaks propagate in one forward pass, and every walk is a loop over an
//! explicit stack. Text is one byte pool; no node owns an allocation.

use crate::tc::graph::NONE;

/// A document handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct D(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Line {
    Classic,
    Soft,
    Hard,
}

/// Twelve bytes; payload ranges index the text pool or the child pool.
#[derive(Clone, Copy, Debug)]
enum Node {
    Nil,
    Text {
        start: u32,
        len: u32,
    },
    Concat {
        start: u32,
        len: u32,
    },
    Indent(D),
    IfBreaks {
        yes: D,
        no: D,
    },
    Line(Line),
    /// The flag of a group is its `should_break` cell.
    Group(D),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    Break,
    Flat,
}

/// One render command: twelve bytes.
#[derive(Clone, Copy)]
struct Cmd {
    indent: i32,
    doc: D,
    mode: Mode,
}

#[derive(Default)]
pub(super) struct Docs {
    nodes: Vec<Node>,
    /// Per node: a group's `should_break`, an `IfBreaks`'s `broken`.
    flags: Vec<bool>,
    kids: Vec<D>,
    text: String,
}

impl Docs {
    /// Amortized O(1).
    fn push(&mut self, node: Node, flag: bool) -> D {
        let d = D(u32::try_from(self.nodes.len()).expect("document node limit"));
        assert!(d.0 != NONE);
        self.nodes.push(node);
        self.flags.push(flag);
        d
    }

    /// O(1).
    pub fn nil(&mut self) -> D {
        self.push(Node::Nil, false)
    }

    /// Amortized O(text): literal text without newlines.
    pub fn text(&mut self, text: &str) -> D {
        let start = u32::try_from(self.text.len()).expect("document text limit");
        self.text.push_str(text);
        let len = text.len() as u32;
        self.push(Node::Text { start, len }, false)
    }

    /// Amortized O(text bytes), writing directly into the shared text pool.
    pub fn formatted(&mut self, args: std::fmt::Arguments<'_>) -> D {
        use std::fmt::Write;
        let start = u32::try_from(self.text.len()).expect("document text limit");
        self.text.write_fmt(args).expect("writing to a string");
        let len = u32::try_from(self.text.len()).expect("document text limit") - start;
        self.push(Node::Text { start, len }, false)
    }

    /// Amortized O(children).
    pub fn concat(&mut self, children: &[D]) -> D {
        let start = u32::try_from(self.kids.len()).expect("document child limit");
        self.kids.extend_from_slice(children);
        self.push(
            Node::Concat {
                start,
                len: children.len() as u32,
            },
            false,
        )
    }

    /// Amortized O(children): `Doc.join sep children`.
    pub fn join(&mut self, sep: D, children: &[D]) -> D {
        let start = u32::try_from(self.kids.len()).expect("document child limit");
        for (index, child) in children.iter().enumerate() {
            if index > 0 {
                self.kids.push(sep);
            }
            self.kids.push(*child);
        }
        let len = self.kids.len() as u32 - start;
        self.push(Node::Concat { start, len }, false)
    }

    /// O(1).
    pub fn indent(&mut self, doc: D) -> D {
        self.push(Node::Indent(doc), false)
    }

    /// O(1).
    pub fn if_breaks(&mut self, yes: D, no: D) -> D {
        self.push(Node::IfBreaks { yes, no }, false)
    }

    /// O(1).
    pub fn line(&mut self) -> D {
        self.push(Node::Line(Line::Classic), false)
    }

    /// O(1).
    pub fn soft_line(&mut self) -> D {
        self.push(Node::Line(Line::Soft), false)
    }

    /// O(1).
    pub fn hard_line(&mut self) -> D {
        self.push(Node::Line(Line::Hard), false)
    }

    /// O(1).
    pub fn group(&mut self, doc: D) -> D {
        self.push(Node::Group(doc), false)
    }

    /// O(1): `Doc.breakable_group ~force_break doc`.
    pub fn breakable_group(&mut self, doc: D, force_break: bool) -> D {
        self.push(Node::Group(doc), force_break)
    }

    /// O(1): `Doc.trailing_comma`.
    pub fn trailing_comma(&mut self) -> D {
        let comma = self.text(",");
        let nil = self.nil();
        self.if_breaks(comma, nil)
    }

    /// O(nodes + children): `propagate_forced_breaks` in one forward pass.
    /// Every node's children are older than it, so a node's value is final
    /// when it is reached; each shared node computes once what every one of
    /// its occurrences computes.
    fn propagate(&mut self) {
        let mut forces = vec![false; self.nodes.len()];
        for index in 0..self.nodes.len() {
            let value = match self.nodes[index] {
                Node::Nil | Node::Text { .. } => false,
                Node::Line(Line::Hard) => true,
                Node::Line(_) => false,
                Node::Indent(child) => forces[child.0 as usize],
                Node::IfBreaks { yes, no } => {
                    if forces[no.0 as usize] {
                        self.flags[index] = true;
                        true
                    } else {
                        forces[yes.0 as usize]
                    }
                }
                Node::Group(child) => {
                    let should = self.flags[index] || forces[child.0 as usize];
                    self.flags[index] = should;
                    should
                }
                Node::Concat { start, len } => self.kids[start as usize..(start + len) as usize]
                    .iter()
                    .any(|child| forces[child.0 as usize]),
            };
            forces[index] = value;
        }
    }

    /// O(text bytes): parser/doc.rs `text_width`: a code point up to U+00FF is one
    /// column, a wider one its UTF-8 length.
    fn width(&self, start: u32, len: u32) -> i32 {
        let text = &self.text[start as usize..(start + len) as usize];
        if text.is_ascii() {
            return text.len() as i32;
        }
        text.chars()
            .map(|c| {
                if (c as u32) <= 0xFF {
                    1
                } else {
                    c.len_utf8() as i32
                }
            })
            .sum()
    }

    /// O(commands examined): `Res_doc.fits` (parser/doc.rs `fits`): `first`,
    /// then the render stack `rest` from its top, until the answer is known.
    fn fits(&self, width: i32, first: Cmd, rest: &[Cmd], stack: &mut Vec<Cmd>) -> bool {
        let mut width = width;
        stack.clear();
        stack.push(first);
        let mut rest = rest.iter().rev();
        loop {
            let cmd = match stack.pop() {
                Some(cmd) => cmd,
                None => match rest.next() {
                    Some(cmd) => *cmd,
                    None => break,
                },
            };
            if width < 0 {
                return false;
            }
            let Cmd { indent, doc, mode } = cmd;
            match self.nodes[doc.0 as usize] {
                Node::Nil => {}
                Node::Text { start, len } => width -= self.width(start, len),
                Node::Indent(child) => stack.push(Cmd {
                    indent: indent + 2,
                    doc: child,
                    mode,
                }),
                Node::Line(Line::Hard) => return true,
                Node::Line(Line::Classic) if mode == Mode::Flat => width -= 1,
                Node::Line(Line::Soft) if mode == Mode::Flat => {}
                Node::Line(_) => return true,
                Node::Group(child) => stack.push(Cmd {
                    indent,
                    doc: child,
                    mode: if self.flags[doc.0 as usize] {
                        Mode::Break
                    } else {
                        mode
                    },
                }),
                Node::IfBreaks { yes, no } => stack.push(Cmd {
                    indent,
                    doc: if self.flags[doc.0 as usize] || mode == Mode::Break {
                        yes
                    } else {
                        no
                    },
                    mode,
                }),
                Node::Concat { start, len } => {
                    for child in self.kids[start as usize..(start + len) as usize]
                        .iter()
                        .rev()
                    {
                        stack.push(Cmd {
                            indent,
                            doc: *child,
                            mode,
                        });
                    }
                }
            }
        }
        width >= 0
    }

    /// O(commands · fits lookahead): `Res_doc.to_string ~width` (parser/doc.rs
    /// `to_string_with_newline` with LF). A hard line in flat mode starts the
    /// next line unindented, as there.
    pub fn render(&mut self, root: D, width: i32) -> String {
        self.propagate();
        let mut out = String::with_capacity(self.text.len() + 64);
        let mut pos = 0i32;
        let mut stack = vec![Cmd {
            indent: 0,
            doc: root,
            mode: Mode::Flat,
        }];
        let mut scratch = Vec::new();
        while let Some(Cmd { indent, doc, mode }) = stack.pop() {
            match self.nodes[doc.0 as usize] {
                Node::Nil => {}
                Node::Text { start, len } => {
                    out.push_str(&self.text[start as usize..(start + len) as usize]);
                    pos += self.width(start, len);
                }
                Node::Concat { start, len } => {
                    for child in self.kids[start as usize..(start + len) as usize]
                        .iter()
                        .rev()
                    {
                        stack.push(Cmd {
                            indent,
                            doc: *child,
                            mode,
                        });
                    }
                }
                Node::Indent(child) => stack.push(Cmd {
                    indent: indent + 2,
                    doc: child,
                    mode,
                }),
                Node::IfBreaks { yes, no } => stack.push(Cmd {
                    indent,
                    doc: if self.flags[doc.0 as usize] || mode == Mode::Break {
                        yes
                    } else {
                        no
                    },
                    mode,
                }),
                Node::Line(style) => {
                    if mode == Mode::Break {
                        flush_newline(&mut out);
                        for _ in 0..indent {
                            out.push(' ');
                        }
                        pos = indent;
                    } else {
                        match style {
                            Line::Classic => {
                                out.push(' ');
                                pos += 1;
                            }
                            Line::Hard => {
                                flush_newline(&mut out);
                                pos = 0;
                            }
                            Line::Soft => {}
                        }
                    }
                }
                Node::Group(child) => {
                    let flat = Cmd {
                        indent,
                        doc: child,
                        mode: Mode::Flat,
                    };
                    let fits = !self.flags[doc.0 as usize]
                        && self.fits(width - pos, flat, &stack, &mut scratch);
                    stack.push(Cmd {
                        mode: if fits { Mode::Flat } else { Mode::Break },
                        ..flat
                    });
                }
            }
        }
        out
    }
}

/// O(trailing spaces): `Mini_buffer.flush_newline`.
fn flush_newline(out: &mut String) {
    let trimmed = out.trim_end_matches(' ').len();
    out.truncate(trimmed);
    out.push('\n');
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Node>(), 12);
        assert_eq!(std::mem::size_of::<Cmd>(), 12);
        assert_eq!(std::mem::size_of::<D>(), 4);
    }

    #[test]
    fn a_group_breaks_when_it_does_not_fit() {
        let mut docs = Docs::default();
        let words: Vec<D> = (0..30).map(|i| docs.text(&format!("word{i}"))).collect();
        let sep = {
            let comma = docs.text(",");
            let line = docs.line();
            docs.concat(&[comma, line])
        };
        let body = docs.join(sep, &words);
        let soft = docs.soft_line();
        let inner = docs.concat(&[soft, body]);
        let content = docs.indent(inner);
        let open = docs.text("(");
        let close = docs.text(")");
        let soft_end = docs.soft_line();
        let all = docs.concat(&[open, content, soft_end, close]);
        let group = docs.group(all);
        let text = docs.render(group, 80);
        assert!(text.starts_with("(\n  word0,\n  word1,"), "{text}");
        let mut docs = Docs::default();
        let a = docs.text("short");
        let group = docs.group(a);
        assert_eq!(docs.render(group, 80), "short");
    }

    #[test]
    fn ten_thousand_deep_documents_render_on_a_two_mb_stack() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut docs = Docs::default();
                let mut doc = docs.text("x");
                for _ in 0..10000 {
                    let open = docs.text("(");
                    let close = docs.text(")");
                    let soft = docs.soft_line();
                    let all = docs.concat(&[open, soft, doc, close]);
                    doc = docs.group(all);
                }
                let text = docs.render(doc, 80);
                assert_eq!(text.matches('x').count(), 1);
                assert_eq!(text.matches('(').count(), 10000);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
