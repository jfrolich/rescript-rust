//! Pretty-printing document representation.
//!
//! This module implements a document representation for pretty-printing,
//! based on Wadler's "A Prettier Printer" algorithm.
//!
//! The key idea is to build a document tree that describes the structure of the
//! output, then render it to a string respecting a maximum line width.

use std::cell::Cell;
use std::rc::Rc;

/// Line break styles
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LineStyle {
    /// Classic line break - replaced with space when in flat mode
    Classic,
    /// Soft line break - replaced with nothing when in flat mode
    Soft,
    /// Hard line break - always included, forces breaks in parent groups
    Hard,
    /// Literal line break - always included, doesn't increase indentation
    /// Used for template literals, multiline string content
    Literal,
}

/// Rendering mode
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Mode {
    /// Break mode - line breaks are rendered as newlines
    Break,
    /// Flat mode - line breaks are rendered as spaces (Classic) or nothing (Soft)
    Flat,
}

/// A pretty-printing document
#[derive(Debug, Clone)]
pub enum Doc {
    /// Empty document
    Nil,
    /// Literal text
    Text(String),
    /// Concatenation of documents
    Concat(Vec<Doc>),
    /// Indent the document by 2 spaces
    Indent(Box<Doc>),
    /// Different output depending on whether we're in break or flat mode
    IfBreaks {
        yes: Box<Doc>,
        no: Box<Doc>,
        /// When true, always use the `yes` branch
        broken: Rc<Cell<bool>>,
    },
    /// Content to print at the end of the line (before the newline)
    LineSuffix(Box<Doc>),
    /// A line break with the given style
    LineBreak(LineStyle),
    /// A group that can be broken or kept flat
    Group {
        /// Whether this group should be broken (forced or computed)
        should_break: Rc<Cell<bool>>,
        /// The document inside the group
        doc: Box<Doc>,
    },
    /// Multiple layout choices - picks first that fits, or last if none fit
    CustomLayout(Vec<Doc>),
    /// Force the parent group to break
    BreakParent,
    /// `Res_doc.ItemSeparator {prev; next}`: a hard line, and a blank line
    /// when `prev` or `next`, the documents printed on each side of it, span
    /// several lines. It measures them but does not print them.
    ItemSeparator { prev: Rc<Doc>, next: Rc<Doc> },
    /// `Res_doc.Comment`: prints like its argument, which an item separator
    /// does not measure.
    Comment(Box<Doc>),
    /// A document that an item separator measures as well: OCaml shares the
    /// document physically between the list and the separators next to it.
    Shared(Rc<Doc>),
}

impl Doc {
    // ========== Constructors ==========

    pub fn nil() -> Doc {
        Doc::Nil
    }

    pub fn text(s: impl Into<String>) -> Doc {
        Doc::Text(s.into())
    }

    pub fn line() -> Doc {
        Doc::LineBreak(LineStyle::Classic)
    }

    pub fn soft_line() -> Doc {
        Doc::LineBreak(LineStyle::Soft)
    }

    pub fn hard_line() -> Doc {
        Doc::LineBreak(LineStyle::Hard)
    }

    pub fn literal_line() -> Doc {
        Doc::LineBreak(LineStyle::Literal)
    }

    /// Concatenate documents, with optimization to collapse nested concats and remove nils
    pub fn concat(docs: Vec<Doc>) -> Doc {
        let mut result = Vec::with_capacity(docs.len());
        for doc in docs {
            match doc {
                Doc::Nil => {}
                Doc::Concat(inner) => result.extend(inner),
                other => result.push(other),
            }
        }
        if result.is_empty() {
            Doc::Nil
        } else if result.len() == 1 {
            result.pop().unwrap()
        } else {
            Doc::Concat(result)
        }
    }

    pub fn indent(doc: Doc) -> Doc {
        Doc::Indent(Box::new(doc))
    }

    pub fn if_breaks(yes: Doc, no: Doc) -> Doc {
        Doc::IfBreaks {
            yes: Box::new(yes),
            no: Box::new(no),
            broken: Rc::new(Cell::new(false)),
        }
    }

    pub fn line_suffix(doc: Doc) -> Doc {
        Doc::LineSuffix(Box::new(doc))
    }

    pub fn group(doc: Doc) -> Doc {
        Doc::Group {
            should_break: Rc::new(Cell::new(false)),
            doc: Box::new(doc),
        }
    }

    pub fn breakable_group(doc: Doc, force_break: bool) -> Doc {
        Doc::Group {
            should_break: Rc::new(Cell::new(force_break)),
            doc: Box::new(doc),
        }
    }

    pub fn custom_layout(layouts: Vec<Doc>) -> Doc {
        Doc::CustomLayout(layouts)
    }

    pub fn break_parent() -> Doc {
        Doc::BreakParent
    }

    /// `Res_doc.item_separator ~prev ~next`.
    pub fn item_separator(prev: Rc<Doc>, next: Rc<Doc>) -> Doc {
        Doc::ItemSeparator { prev, next }
    }

    /// `Res_doc.comment`.
    pub fn comment(doc: Doc) -> Doc {
        Doc::Comment(Box::new(doc))
    }

    /// `Res_doc.is_nil`.
    pub fn is_nil(&self) -> bool {
        matches!(self, Doc::Nil)
    }

    // ========== Common combinators ==========

    pub fn space() -> Doc {
        Doc::text(" ")
    }

    pub fn comma() -> Doc {
        Doc::text(",")
    }

    pub fn dot() -> Doc {
        Doc::text(".")
    }

    pub fn dotdot() -> Doc {
        Doc::text("..")
    }

    pub fn dotdotdot() -> Doc {
        Doc::text("...")
    }

    pub fn less_than() -> Doc {
        Doc::text("<")
    }

    pub fn greater_than() -> Doc {
        Doc::text(">")
    }

    pub fn lbrace() -> Doc {
        Doc::text("{")
    }

    pub fn rbrace() -> Doc {
        Doc::text("}")
    }

    pub fn lparen() -> Doc {
        Doc::text("(")
    }

    pub fn rparen() -> Doc {
        Doc::text(")")
    }

    pub fn lbracket() -> Doc {
        Doc::text("[")
    }

    pub fn rbracket() -> Doc {
        Doc::text("]")
    }

    pub fn question() -> Doc {
        Doc::text("?")
    }

    pub fn tilde() -> Doc {
        Doc::text("~")
    }

    pub fn equal() -> Doc {
        Doc::text("=")
    }

    pub fn double_quote() -> Doc {
        Doc::text("\"")
    }

    /// A trailing comma that only appears when the group is broken
    pub fn trailing_comma() -> Doc {
        Doc::if_breaks(Doc::comma(), Doc::nil())
    }

    /// Join documents with a separator
    pub fn join(sep: Doc, docs: Vec<Doc>) -> Doc {
        let mut result = Vec::with_capacity(docs.len() * 2);
        let mut first = true;
        for doc in docs {
            if !first {
                result.push(sep.clone());
            }
            first = false;
            result.push(doc);
        }
        Doc::concat(result)
    }

    /// Join documents with separators that may differ per element
    pub fn join_with_sep(docs_with_sep: Vec<(Doc, Doc)>) -> Doc {
        let mut result = Vec::with_capacity(docs_with_sep.len() * 2);
        let len = docs_with_sep.len();
        for (i, (doc, sep)) in docs_with_sep.into_iter().enumerate() {
            result.push(doc);
            if i < len - 1 {
                result.push(sep);
            }
        }
        Doc::concat(result)
    }

    // ========== Rendering ==========

    /// Propagate forced breaks up through the document tree.
    /// This sets the `should_break` flag on groups that contain hard breaks.
    pub fn propagate_forced_breaks(&self) -> bool {
        match self {
            Doc::Text(_) | Doc::Nil | Doc::LineSuffix(_) => false,
            Doc::BreakParent => true,
            Doc::LineBreak(LineStyle::Hard)
            | Doc::LineBreak(LineStyle::Literal)
            | Doc::ItemSeparator { .. } => true,
            Doc::LineBreak(LineStyle::Classic) | Doc::LineBreak(LineStyle::Soft) => false,
            Doc::Indent(child) | Doc::Comment(child) => child.propagate_forced_breaks(),
            Doc::Shared(child) => child.propagate_forced_breaks(),
            Doc::IfBreaks { yes, no, broken } => {
                let no_forces = no.propagate_forced_breaks();
                if no_forces {
                    yes.propagate_forced_breaks();
                    broken.set(true);
                    true
                } else {
                    yes.propagate_forced_breaks()
                }
            }
            Doc::Group { should_break, doc } => {
                let child_forces = doc.propagate_forced_breaks();
                let should = should_break.get() || child_forces;
                should_break.set(should);
                should
            }
            Doc::Concat(children) => {
                let mut forces = false;
                for child in children {
                    if child.propagate_forced_breaks() {
                        forces = true;
                    }
                }
                forces
            }
            Doc::CustomLayout(children) => {
                // Don't propagate forced breaks up from CustomLayout,
                // but do propagate within sublayouts
                for child in children {
                    child.propagate_forced_breaks();
                }
                false
            }
        }
    }

    /// Check if the document will definitely break (contains hard breaks or forced groups)
    pub fn will_break(&self) -> bool {
        match self {
            Doc::LineBreak(LineStyle::Hard) | Doc::LineBreak(LineStyle::Literal) => true,
            Doc::BreakParent | Doc::ItemSeparator { .. } => true,
            Doc::Group { should_break, .. } if should_break.get() => true,
            Doc::Group { doc, .. } => doc.will_break(),
            Doc::Indent(doc) | Doc::Comment(doc) => doc.will_break(),
            Doc::Shared(doc) => doc.will_break(),
            Doc::CustomLayout(docs) if !docs.is_empty() => docs[0].will_break(),
            Doc::Concat(docs) => docs.iter().any(|d| d.will_break()),
            Doc::IfBreaks { yes, no, .. } => yes.will_break() || no.will_break(),
            _ => false,
        }
    }

    /// Whether a line suffix (a trailing line comment) in the document is still
    /// queued at its end, because no line break of a group that breaks follows
    /// it (`Res_doc.has_pending_line_suffix`, res_doc.ml:133-149). Groups that
    /// only break for lack of width count as flat. Text after the document on
    /// the same line would precede the comment.
    pub fn has_pending_line_suffix(&self) -> bool {
        // `pending`: a line suffix is queued; `broken`: the innermost
        // enclosing group is printed in break mode, so its line breaks flush
        // the queue.
        fn walk(doc: &Doc, broken: bool, pending: bool) -> bool {
            match doc {
                Doc::LineSuffix(_) => true,
                Doc::LineBreak(_) | Doc::ItemSeparator { .. } => pending && !broken,
                Doc::Nil | Doc::Text(_) | Doc::BreakParent => pending,
                Doc::Indent(doc) | Doc::Comment(doc) => walk(doc, broken, pending),
                Doc::Shared(doc) => walk(doc, broken, pending),
                Doc::Concat(docs) => docs
                    .iter()
                    .fold(pending, |pending, doc| walk(doc, broken, pending)),
                Doc::Group { should_break, doc } => {
                    walk(doc, should_break.get() || doc.will_break(), pending)
                }
                Doc::IfBreaks {
                    yes,
                    no,
                    broken: if_broken,
                } => walk(
                    if broken || if_broken.get() { yes } else { no },
                    broken,
                    pending,
                ),
                Doc::CustomLayout(docs) => docs.iter().any(|doc| walk(doc, false, pending)),
            }
        }
        walk(self, false, false)
    }

    /// Check if the document fits within the given width.
    ///
    /// Mirrors `Res_doc.fits` (`compiler/syntax/src/res_doc.ml:169-213`):
    /// `first` is processed, then the entries of `rest` from the top of the
    /// render stack downwards, stopping as soon as the result is known. `rest`
    /// is walked lazily so a check never copies the whole render stack.
    fn fits(width: i32, first: (i32, Mode, &Doc), rest: &[(i32, Mode, &Doc)]) -> bool {
        let mut width = width;
        let mut stack: Vec<(i32, Mode, &Doc)> = vec![first];
        let mut rest = rest.iter().rev();

        loop {
            let (indent, mode, doc) = match stack.pop() {
                Some(item) => item,
                None => match rest.next() {
                    Some(item) => *item,
                    None => break,
                },
            };
            if width < 0 {
                return false;
            }

            match (mode, doc) {
                (_, Doc::Nil) | (_, Doc::LineSuffix(_)) | (_, Doc::BreakParent) => {}
                (_, Doc::Text(txt)) => {
                    width -= text_width(txt);
                }
                (_, Doc::Indent(doc)) => {
                    stack.push((indent + 2, mode, doc));
                }
                (_, Doc::Comment(doc)) => {
                    stack.push((indent, mode, doc));
                }
                (_, Doc::Shared(doc)) => {
                    stack.push((indent, mode, doc));
                }
                (Mode::Flat, Doc::LineBreak(LineStyle::Hard))
                | (Mode::Flat, Doc::LineBreak(LineStyle::Literal)) => {
                    return true;
                }
                (Mode::Flat, Doc::LineBreak(LineStyle::Classic)) => {
                    width -= 1;
                }
                (Mode::Flat, Doc::LineBreak(LineStyle::Soft)) => {}
                (Mode::Break, Doc::LineBreak(_)) => {
                    return true;
                }
                (_, Doc::ItemSeparator { .. }) => {
                    return true;
                }
                (_, Doc::Group { should_break, doc }) if should_break.get() => {
                    stack.push((indent, Mode::Break, doc));
                }
                (_, Doc::Group { doc, .. }) => {
                    stack.push((indent, mode, doc));
                }
                (_, Doc::IfBreaks { yes, broken, .. }) if broken.get() => {
                    stack.push((indent, mode, yes));
                }
                (Mode::Break, Doc::IfBreaks { yes, .. }) => {
                    stack.push((indent, mode, yes));
                }
                (Mode::Flat, Doc::IfBreaks { no, .. }) => {
                    stack.push((indent, mode, no));
                }
                (_, Doc::Concat(docs)) => {
                    // Push in reverse order so first doc is processed first
                    for doc in docs.iter().rev() {
                        stack.push((indent, mode, doc));
                    }
                }
                (_, Doc::CustomLayout(docs)) if !docs.is_empty() => {
                    stack.push((indent, mode, &docs[0]));
                }
                (_, Doc::CustomLayout(_)) => {}
            }
        }

        width >= 0
    }

    /// `Res_doc.select_custom_layout` (res_doc.ml:215-224): the first layout
    /// that fits, the last one when none before it fits, `None` (OCaml `Nil`)
    /// when there is none.
    fn select_custom_layout<'d>(
        width: i32,
        pos: i32,
        indent: i32,
        rest: &[(i32, Mode, &'d Doc)],
        docs: &'d [Doc],
    ) -> Option<&'d Doc> {
        let (last, init) = docs.split_last()?;
        Some(
            init.iter()
                .find(|doc| Self::fits(width - pos, (indent, Mode::Flat, doc), rest))
                .unwrap_or(last),
        )
    }

    /// `Res_doc.spans_lines` (res_doc.ml:226-256): whether `doc`, printed from
    /// the start of a line indented by `indent`, spans more than one line.
    /// Takes the layout decisions of `to_string` up to the first line break.
    /// Comments and line suffixes do not count.
    fn spans_lines(width: i32, indent: i32, mode: Mode, doc: &Doc) -> bool {
        let mut pos = indent;
        let mut stack: Vec<(i32, Mode, &Doc)> = vec![(indent, mode, doc)];
        while let Some((indent, mode, doc)) = stack.pop() {
            match doc {
                Doc::Nil | Doc::BreakParent | Doc::LineSuffix(_) | Doc::Comment(_) => {}
                Doc::Text(txt) => {
                    if txt.contains('\n') {
                        return true;
                    }
                    pos += text_width(txt);
                }
                Doc::Concat(docs) => {
                    for doc in docs.iter().rev() {
                        stack.push((indent, mode, doc));
                    }
                }
                Doc::Indent(doc) => stack.push((indent + 2, mode, doc)),
                Doc::Shared(doc) => stack.push((indent, mode, doc)),
                Doc::IfBreaks { yes, no, broken } => {
                    let doc = if broken.get() || mode == Mode::Break {
                        yes
                    } else {
                        no
                    };
                    stack.push((indent, mode, doc));
                }
                Doc::LineBreak(LineStyle::Hard | LineStyle::Literal)
                | Doc::ItemSeparator { .. } => {
                    return true;
                }
                Doc::LineBreak(LineStyle::Classic) => {
                    if mode == Mode::Break {
                        return true;
                    }
                    pos += 1;
                }
                Doc::LineBreak(LineStyle::Soft) => {
                    if mode == Mode::Break {
                        return true;
                    }
                }
                Doc::Group { should_break, doc } => {
                    if should_break.get()
                        || !Self::fits(width - pos, (indent, Mode::Flat, doc), &stack)
                    {
                        stack.push((indent, Mode::Break, doc));
                    } else {
                        stack.push((indent, Mode::Flat, doc));
                    }
                }
                Doc::CustomLayout(docs) => {
                    if let Some(doc) = Self::select_custom_layout(width, pos, indent, &stack, docs)
                    {
                        stack.push((indent, Mode::Flat, doc));
                    }
                }
            }
        }
        false
    }

    /// `Res_doc.own_line_suffix` (res_doc.ml:258-266): an own-line trailing
    /// comment is a line suffix that starts with a hard line; returns the
    /// documents it concatenates after its leading hard lines.
    fn own_line_suffix(&self) -> Option<&[Doc]> {
        match self {
            Doc::LineBreak(LineStyle::Hard) => Some(&[]),
            Doc::Concat(docs) if matches!(docs.first(), Some(Doc::LineBreak(LineStyle::Hard))) => {
                let hard_lines = docs
                    .iter()
                    .take_while(|doc| matches!(doc, Doc::LineBreak(LineStyle::Hard)))
                    .count();
                Some(&docs[hard_lines..])
            }
            _ => None,
        }
    }

    /// Render the document to a string with the given maximum line width,
    /// its line breaks written as LF (`Res_doc.to_string ~width`).
    pub fn to_string(&self, width: i32) -> String {
        self.to_string_with_newline(width, "\n")
    }

    /// `Res_doc.to_string ~newline ~width` (res_doc.ml:268-357): the line
    /// breaks the printer writes are `newline`; a literal line is part of a
    /// literal's contents and stays LF.
    pub fn to_string_with_newline(&self, width: i32, newline: &str) -> String {
        self.propagate_forced_breaks();

        let hard_line = Doc::hard_line();
        let mut buffer = String::with_capacity(1024);
        let mut pos = 0i32;
        // `line_suffices`, oldest first: OCaml conses each new suffix and
        // reverses the list when it flushes them.
        let mut line_suffices: Vec<(i32, Mode, &Doc)> = Vec::new();
        let mut stack: Vec<(i32, Mode, &Doc)> = vec![(0, Mode::Flat, self)];

        // `Mini_buffer.flush_newline`: trim the spaces before the line break.
        fn flush_newline(buffer: &mut String, newline: &str) {
            let trimmed_len = buffer.trim_end_matches(' ').len();
            buffer.truncate(trimmed_len);
            buffer.push_str(newline);
        }

        loop {
            let Some((indent, mode, doc)) = stack.pop() else {
                // `| [] -> process ~pos:0 [] (List.rev suffices)`
                if line_suffices.is_empty() {
                    break;
                }
                for suffix in line_suffices.drain(..).rev() {
                    stack.push(suffix);
                }
                pos = 0;
                continue;
            };
            match doc {
                Doc::Nil | Doc::BreakParent => {}
                Doc::Text(txt) => {
                    buffer.push_str(txt);
                    pos += text_width(txt);
                }
                Doc::LineSuffix(doc) => {
                    line_suffices.push((indent, mode, doc));
                }
                Doc::Concat(docs) => {
                    for doc in docs.iter().rev() {
                        stack.push((indent, mode, doc));
                    }
                }
                Doc::Indent(doc) => {
                    stack.push((indent + 2, mode, doc));
                }
                Doc::Comment(doc) => {
                    stack.push((indent, mode, doc));
                }
                Doc::Shared(doc) => {
                    stack.push((indent, mode, doc));
                }
                Doc::IfBreaks { yes, broken, .. } if broken.get() => {
                    stack.push((indent, mode, yes));
                }
                Doc::IfBreaks { yes, no, .. } => {
                    if mode == Mode::Break {
                        stack.push((indent, mode, yes));
                    } else {
                        stack.push((indent, mode, no));
                    }
                }
                Doc::LineBreak(style) => {
                    if mode == Mode::Break {
                        if !line_suffices.is_empty() {
                            // `process ~pos:ind [] (List.concat [List.rev
                            // line_suffices; cmd :: rest])`
                            stack.push((indent, mode, doc));
                            for suffix in line_suffices.drain(..).rev() {
                                stack.push(suffix);
                            }
                            pos = indent;
                        } else if *style == LineStyle::Literal {
                            buffer.push('\n');
                            pos = 0;
                        } else {
                            flush_newline(&mut buffer, newline);
                            for _ in 0..indent {
                                buffer.push(' ');
                            }
                            pos = indent;
                        }
                    } else {
                        match style {
                            LineStyle::Classic => {
                                buffer.push(' ');
                                pos += 1;
                            }
                            LineStyle::Hard => {
                                flush_newline(&mut buffer, newline);
                                pos = 0;
                            }
                            LineStyle::Literal => {
                                buffer.push('\n');
                                pos = 0;
                            }
                            LineStyle::Soft => {}
                        }
                    }
                }
                Doc::Group { should_break, doc } => {
                    if should_break.get()
                        || !Self::fits(width - pos, (indent, Mode::Flat, doc), &stack)
                    {
                        stack.push((indent, Mode::Break, doc));
                    } else {
                        stack.push((indent, Mode::Flat, doc));
                    }
                }
                Doc::CustomLayout(docs) => {
                    if let Some(doc) = Self::select_custom_layout(width, pos, indent, &stack, docs)
                    {
                        stack.push((indent, Mode::Flat, doc));
                    }
                }
                Doc::ItemSeparator { prev, next } => {
                    if Self::spans_lines(width, indent, mode, prev)
                        || Self::spans_lines(width, indent, mode, next)
                    {
                        // Own-line trailing comments of `prev` go below the
                        // blank line, where they print once they are leading
                        // comments of `next` (res_doc.ml:330-351). The stack
                        // grows towards its top, so the commands go on in
                        // reverse: the two separators, the first comment
                        // without its hard lines, the other comments as they
                        // are, a separator, then what follows.
                        let mut same_line = Vec::with_capacity(line_suffices.len());
                        let mut below: Vec<(&[Doc], (i32, Mode, &Doc))> = Vec::new();
                        for suffix in line_suffices.drain(..) {
                            match suffix.2.own_line_suffix() {
                                None => same_line.push(suffix),
                                Some(comment) => below.push((comment, suffix)),
                            }
                        }
                        line_suffices = same_line;
                        if let Some(((first, (first_indent, first_mode, _)), others)) =
                            below.split_first()
                        {
                            stack.push((indent, mode, &hard_line));
                            for (_, suffix) in others.iter().rev() {
                                stack.push(*suffix);
                            }
                            for doc in first.iter().rev() {
                                stack.push((*first_indent, *first_mode, doc));
                            }
                        }
                        stack.push((indent, mode, &hard_line));
                        stack.push((indent, mode, &hard_line));
                    } else {
                        stack.push((indent, mode, &hard_line));
                    }
                }
            }
        }

        buffer
    }
}

/// The width res_doc.ml:152,198 gives a text: OCaml's `String.length`, a
/// byte count of the source. Printer text carries source bytes as Latin-1
/// chars (one char per byte); other chars count as their UTF-8 bytes.
fn text_width(txt: &str) -> i32 {
    if txt.is_ascii() {
        return txt.len() as i32;
    }
    txt.chars()
        .map(|c| {
            if (c as u32) <= 0xFF {
                1
            } else {
                c.len_utf8() as i32
            }
        })
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_text() {
        let doc = Doc::text("hello");
        assert_eq!(doc.to_string(80), "hello");
    }

    #[test]
    fn test_concat() {
        let doc = Doc::concat(vec![Doc::text("hello"), Doc::space(), Doc::text("world")]);
        assert_eq!(doc.to_string(80), "hello world");
    }

    #[test]
    fn test_group_fits() {
        let doc = Doc::group(Doc::concat(vec![
            Doc::text("hello"),
            Doc::line(),
            Doc::text("world"),
        ]));
        assert_eq!(doc.to_string(80), "hello world");
    }

    #[test]
    fn test_group_breaks() {
        let doc = Doc::group(Doc::concat(vec![
            Doc::text("hello"),
            Doc::line(),
            Doc::text("world"),
        ]));
        assert_eq!(doc.to_string(5), "hello\nworld");
    }

    #[test]
    fn test_indent() {
        let doc = Doc::group(Doc::concat(vec![
            Doc::text("{"),
            Doc::indent(Doc::concat(vec![Doc::line(), Doc::text("x")])),
            Doc::line(),
            Doc::text("}"),
        ]));
        assert_eq!(doc.to_string(3), "{\n  x\n}");
    }

    #[test]
    fn test_trailing_comma() {
        let doc = Doc::group(Doc::concat(vec![
            Doc::text("["),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::text("a"),
                Doc::text(","),
                Doc::line(),
                Doc::text("b"),
                Doc::trailing_comma(),
            ])),
            Doc::soft_line(),
            Doc::text("]"),
        ]));
        // When fits: [a, b]
        assert_eq!(doc.to_string(80), "[a, b]");
        // When breaks: [\n  a,\n  b,\n]
        assert_eq!(doc.to_string(5), "[\n  a,\n  b,\n]");
    }

    #[test]
    fn test_double_hard_line() {
        // Test that two consecutive hard_lines produce a blank line
        let doc = Doc::concat(vec![
            Doc::text("a"),
            Doc::hard_line(),
            Doc::hard_line(),
            Doc::text("b"),
        ]);
        assert_eq!(doc.to_string(80), "a\n\nb");
    }

    #[test]
    fn test_double_hard_line_in_breakable_group() {
        // Test that two consecutive hard_lines work inside breakable_group
        let doc = Doc::breakable_group(
            Doc::concat(vec![
                Doc::text("a"),
                Doc::hard_line(),
                Doc::hard_line(),
                Doc::text("b"),
            ]),
            true,
        );
        assert_eq!(doc.to_string(80), "a\n\nb");
    }

    #[test]
    fn test_fits_has_no_iteration_cap() {
        // OCaml `Res_doc.fits` has no node budget: a group with many zero-width
        // nodes before its text still fits on one line.
        let mut docs: Vec<Doc> = (0..20_000).map(|_| Doc::soft_line()).collect();
        docs.extend([Doc::text("a"), Doc::line(), Doc::text("b")]);
        let doc = Doc::group(Doc::concat(docs));
        assert_eq!(doc.to_string(80), "a b");
    }

    #[test]
    fn test_fits_checks_rest_of_stack() {
        // The text following a group counts towards whether the group fits.
        let doc = Doc::concat(vec![
            Doc::group(Doc::concat(vec![
                Doc::text("hello"),
                Doc::line(),
                Doc::text("world"),
            ])),
            Doc::text("!!!!"),
        ]);
        assert_eq!(doc.to_string(13), "hello\nworld!!!!");
        assert_eq!(doc.to_string(15), "hello world!!!!");
    }

    // tests/syntax_tests/res_test.ml:650-780 (Multiline_item_spacing_test):
    // `item_separator` puts a blank line next to an item that prints on
    // several lines, measuring the documents on each side as `to_string`
    // lays them out; `comment` hides comments from the measurement.

    /// Module items are printed inside a broken group, like print_structure.
    fn print_items(width: i32, doc: Doc) -> String {
        Doc::breakable_group(doc, true).to_string(width)
    }

    fn items(prev: Doc, next: Doc) -> Doc {
        let prev = Rc::new(prev);
        let next = Rc::new(next);
        Doc::concat(vec![
            Doc::Shared(prev.clone()),
            Doc::item_separator(prev, next.clone()),
            Doc::Shared(next),
        ])
    }

    fn item_a() -> Doc {
        Doc::text("let a = 1")
    }

    fn item_b() -> Doc {
        Doc::text("let b = 2")
    }

    /// A function call that fits on one line at width 80 but not at width 5.
    fn call() -> Doc {
        Doc::group(Doc::concat(vec![
            Doc::text("f("),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::text("x,"),
                Doc::line(),
                Doc::text("y"),
                Doc::trailing_comma(),
            ])),
            Doc::soft_line(),
            Doc::text(")"),
        ]))
    }

    #[test]
    fn item_separator_measures_items() {
        assert_eq!(
            print_items(80, items(item_a(), item_b())),
            "let a = 1\nlet b = 2"
        );
        assert_eq!(
            print_items(
                80,
                items(
                    Doc::concat(vec![Doc::text("x"), Doc::hard_line(), Doc::text("y")]),
                    item_b()
                )
            ),
            "x\ny\n\nlet b = 2"
        );
        assert_eq!(
            print_items(
                80,
                items(
                    Doc::concat(vec![Doc::text("`x"), Doc::literal_line(), Doc::text("y`")]),
                    item_b()
                )
            ),
            "`x\ny`\n\nlet b = 2"
        );
        assert_eq!(
            print_items(80, items(Doc::text("`x\ny`"), item_b())),
            "`x\ny`\n\nlet b = 2"
        );
        assert_eq!(
            print_items(80, items(items(item_a(), item_b()), Doc::text("let c = 3"))),
            "let a = 1\nlet b = 2\n\nlet c = 3"
        );
        assert_eq!(
            print_items(80, items(call(), item_b())),
            "f(x, y)\nlet b = 2"
        );
        assert_eq!(
            print_items(5, items(call(), item_b())),
            "f(\n  x,\n  y,\n)\n\nlet b = 2"
        );
        assert_eq!(
            print_items(80, items(Doc::custom_layout(vec![item_a()]), item_b())),
            "let a = 1\nlet b = 2"
        );
        assert_eq!(
            print_items(
                80,
                items(
                    Doc::concat(vec![
                        item_a(),
                        Doc::break_parent(),
                        Doc::line_suffix(Doc::text(" // c"))
                    ]),
                    item_b()
                )
            ),
            "let a = 1 // c\nlet b = 2"
        );
        assert_eq!(
            print_items(
                80,
                items(
                    item_a(),
                    Doc::concat(vec![
                        Doc::comment(Doc::concat(vec![Doc::text("// c"), Doc::hard_line()])),
                        item_b()
                    ])
                )
            ),
            "let a = 1\n// c\nlet b = 2"
        );
        let forced_if_breaks = Doc::if_breaks(
            Doc::text("a"),
            Doc::concat(vec![Doc::text("b"), Doc::hard_line()]),
        );
        assert_eq!(
            print_items(
                80,
                items(
                    Doc::concat(vec![Doc::text("x"), forced_if_breaks]),
                    item_b()
                )
            ),
            "xa\nlet b = 2"
        );
        assert_eq!(
            print_items(
                80,
                items(
                    Doc::breakable_group(
                        Doc::concat(vec![
                            Doc::if_breaks(Doc::text("{"), Doc::text("(")),
                            Doc::line(),
                            Doc::text("}"),
                        ]),
                        true
                    ),
                    item_b()
                )
            ),
            "{\n}\n\nlet b = 2"
        );
    }

    #[test]
    fn item_separator_moves_own_line_trailing_comments_below_the_blank_line() {
        let block = || {
            Doc::concat(vec![
                Doc::text("let a = {"),
                Doc::hard_line(),
                Doc::text("}"),
            ])
        };
        let after_block = |suffix: Doc| {
            items(
                Doc::concat(vec![block(), Doc::line_suffix(suffix)]),
                item_b(),
            )
        };
        assert_eq!(
            print_items(80, after_block(Doc::text(" // c"))),
            "let a = {\n} // c\n\nlet b = 2"
        );
        assert_eq!(
            print_items(
                80,
                after_block(Doc::concat(vec![Doc::hard_line(), Doc::text("// c")]))
            ),
            "let a = {\n}\n\n// c\nlet b = 2"
        );
        assert_eq!(
            print_items(80, after_block(Doc::hard_line())),
            "let a = {\n}\n\n\nlet b = 2"
        );
        let own_line =
            |txt: &str| Doc::line_suffix(Doc::concat(vec![Doc::hard_line(), Doc::text(txt)]));
        assert_eq!(
            print_items(
                80,
                items(
                    Doc::concat(vec![block(), own_line("// c"), own_line("// d")]),
                    item_b()
                )
            ),
            "let a = {\n}\n\n// c\n// d\nlet b = 2"
        );
    }

    #[test]
    fn item_separator_predicates() {
        let separator = Doc::item_separator(Rc::new(item_a()), Rc::new(item_b()));
        assert!(separator.will_break());
        assert!(!separator.is_nil());
        // A separator breaks its group, which flushes a pending line suffix.
        assert!(
            !Doc::group(Doc::concat(vec![Doc::line_suffix(item_a()), separator]))
                .has_pending_line_suffix()
        );
        assert_eq!(print_items(80, Doc::custom_layout(vec![])), "");
    }
}
