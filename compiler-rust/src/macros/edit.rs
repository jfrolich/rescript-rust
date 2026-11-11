//! Source text with edits applied and a map back to the original.
//!
//! Macro expansion edits the source text of a file: a macro call is replaced
//! by the code the macro returned, a generated function is inserted before
//! the item that needs it. Every character of the edited text remembers
//! where it comes from, so that diagnostics, source maps and editor tooling
//! keep pointing at what the person wrote:
//!
//! - a character of the file as written has its offset in that file;
//! - a generated character has the macro use it was generated for, and, when
//!   it was written in a quote, the file, line and column of that quote.
//!
//! Offsets are in characters, like `Position::cnum`.

use std::sync::Arc;

/// Code a macro returned: its text, and which parts of it are text from
/// elsewhere.
#[derive(Debug, Clone, Default)]
pub struct Code {
    pub text: String,
    /// In order of `start`, not overlapping.
    pub spans: Vec<Span>,
}

/// The characters `start..start + len` of a [`Code`].
#[derive(Debug, Clone)]
pub struct Span {
    pub start: u32,
    pub len: u32,
    pub from: SpanSource,
}

#[derive(Debug, Clone)]
pub enum SpanSource {
    /// The characters at this offset of the text being edited: an argument
    /// of the macro that it put in its result.
    Text(u32),
    /// A quote, `%code(...)`, in the macro's file. `line` counts from 1,
    /// `column` from 0.
    Quote {
        file: Arc<str>,
        line: u32,
        column: u32,
    },
}

impl Code {
    pub fn plain(text: impl Into<String>) -> Self {
        Code {
            text: text.into(),
            spans: Vec::new(),
        }
    }
}

/// One part of an edit's replacement.
#[derive(Debug, Clone)]
pub enum Segment {
    /// Generated text.
    Text(String),
    /// Generated text with what is known of where it comes from.
    Code(Code),
    /// The characters `start..end` of the text being edited, kept with
    /// where they come from.
    Copy(u32, u32),
    /// The generated text that follows in this edit was generated for the
    /// macro use at `start..end` of the text being edited. Without it, it
    /// was generated for what the edit replaces. With a description, a
    /// diagnostic in that text says what it is: "`Json.encode` for `user`".
    For(u32, u32, Option<Arc<str>>),
}

/// Replace the characters `start..end` by `segments`. An insertion has
/// `start == end`.
#[derive(Debug, Clone)]
pub struct Edit {
    pub start: u32,
    pub end: u32,
    pub segments: Vec<Segment>,
    /// The generated text is the compiler's own rewriting (a lowered quote):
    /// a diagnostic in it does not show it.
    pub internal: bool,
}

impl Edit {
    pub fn replace(start: u32, end: u32, text: impl Into<String>) -> Self {
        Edit::with(start, end, vec![Segment::Text(text.into())])
    }

    pub fn insert(at: u32, text: impl Into<String>) -> Self {
        Edit::replace(at, at, text)
    }

    pub fn with(start: u32, end: u32, segments: Vec<Segment>) -> Self {
        Edit {
            start,
            end,
            segments,
            internal: false,
        }
    }
}

/// The macro use some text was generated for: its range in the source as
/// written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Use {
    start: u32,
    end: u32,
    /// Whether a diagnostic in the generated text shows that text.
    shown: bool,
    /// Index + 1 into `descriptions`; 0 for none.
    description: u32,
}

/// Where a character comes from, besides its offset in the source.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct Mark {
    /// Index + 1 into `uses`; 0 for a character of the source as written.
    use_id: u32,
    /// Index + 1 into `files`; 0 for a character that is not from a quote.
    file: u32,
    line: u32,
    column: u32,
}

/// Where a generated character comes from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generated {
    /// The macro use, in the source as written.
    pub use_start: u32,
    pub use_end: u32,
    /// Whether a diagnostic shows the generated text.
    pub shown: bool,
    /// What the text is, when it is more than the result of the use.
    pub description: Option<Arc<str>>,
    /// The quote the character was written in: file, line (from 1) and
    /// column (from 0).
    pub quote: Option<(Arc<str>, u32, u32)>,
}

/// A file's text during macro expansion.
#[derive(Debug, Clone)]
pub struct SourceText {
    text: String,
    /// Byte offset of each character, and of the end of the text.
    char_to_byte: Vec<u32>,
    /// Offset in the original text of each character, and of the end. For a
    /// generated character: where its macro use starts.
    origin: Vec<u32>,
    /// Per character, and for the end.
    marks: Vec<Mark>,
    uses: Vec<Use>,
    files: Vec<Arc<str>>,
    descriptions: Vec<Arc<str>>,
    /// Whether any edit was applied.
    edited: bool,
}

impl SourceText {
    pub fn new(text: &str) -> Self {
        let char_to_byte = char_offsets(text);
        let chars = char_to_byte.len() as u32 - 1;
        SourceText {
            text: text.to_string(),
            char_to_byte,
            origin: (0..=chars).collect(),
            marks: vec![Mark::default(); chars as usize + 1],
            uses: Vec::new(),
            files: Vec::new(),
            descriptions: Vec::new(),
            edited: false,
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn is_edited(&self) -> bool {
        self.edited
    }

    pub fn len(&self) -> u32 {
        self.char_to_byte.len() as u32 - 1
    }

    /// The characters `start..end`.
    pub fn slice(&self, start: u32, end: u32) -> &str {
        let len = self.len();
        let start = start.min(len);
        let end = end.clamp(start, len);
        &self.text
            [self.char_to_byte[start as usize] as usize..self.char_to_byte[end as usize] as usize]
    }

    /// The offset in the original text of the character at `offset`: for a
    /// generated character, the start of its macro use.
    pub fn origin(&self, offset: u32) -> u32 {
        self.origin[(offset as usize).min(self.origin.len() - 1)]
    }

    /// The offset in the original text where a range that ends before
    /// `offset` ends: for a generated character, the end of its macro use.
    pub fn origin_end(&self, offset: u32) -> u32 {
        if offset == 0 {
            return self.origin(0);
        }
        let last = (offset as usize - 1).min(self.origin.len() - 1);
        match self.marks[last].use_id {
            0 => self.origin[last] + 1,
            id => self.uses[id as usize - 1].end,
        }
    }

    /// Where the character at `offset` comes from, if it is generated.
    pub fn generated(&self, offset: u32) -> Option<Generated> {
        let mark = self.marks[(offset as usize).min(self.marks.len() - 1)];
        if mark.use_id == 0 {
            return None;
        }
        let used = self.uses[mark.use_id as usize - 1];
        Some(Generated {
            use_start: used.start,
            use_end: used.end,
            shown: used.shown,
            description: (used.description != 0)
                .then(|| self.descriptions[used.description as usize - 1].clone()),
            quote: (mark.file != 0).then(|| {
                (
                    self.files[mark.file as usize - 1].clone(),
                    mark.line,
                    mark.column,
                )
            }),
        })
    }

    /// Where the characters `from..to` are in the original text. A range
    /// that starts or ends in generated code covers the macro use the code
    /// was generated for.
    pub fn original_range(&self, from: u32, to: u32) -> (u32, u32) {
        if to <= from {
            let at = self.origin(from);
            return (at, at);
        }
        let first = self.generated(from);
        let last = self.generated(to - 1);
        let mut range = (self.origin(from), self.origin_end(to));
        // The rest of a range that is partly in generated code is an
        // argument of the same use.
        if let Some(last) = &last
            && (first.is_some() || (last.use_start..last.use_end).contains(&range.0))
        {
            range.0 = last.use_start;
        }
        if let Some(first) = &first
            && (last.is_some()
                || (first.use_start..first.use_end).contains(&range.1.saturating_sub(1)))
        {
            range.1 = first.use_end;
        }
        (range.0, range.1.max(range.0))
    }

    /// The generated code that the characters `from..to` are in: `None` for
    /// a range that starts and ends in the source as written, also when it
    /// has a macro use inside it, and for the compiler's own rewriting.
    pub fn generated_code(&self, from: u32, to: u32) -> Option<GeneratedCode> {
        let to = to.clamp(from + 1, self.len().max(from + 1));
        let shown = |offset: u32| self.generated(offset).filter(|generated| generated.shown);
        let description = shown(from).or_else(|| shown(to - 1))?.description;
        let mut quote: Option<QuoteRange> = None;
        for offset in from..to {
            let Some((file, line, column)) =
                self.generated(offset).and_then(|generated| generated.quote)
            else {
                continue;
            };
            match &mut quote {
                None => {
                    quote = Some(QuoteRange {
                        file,
                        start: (line, column),
                        end: (line, column + 1),
                    });
                }
                Some(range) if range.file == file && (line, column) >= range.start => {
                    range.end = (line, column + 1);
                }
                Some(_) => {}
            }
        }
        Some(GeneratedCode {
            start: from,
            end: to,
            description,
            quote,
        })
    }

    /// Apply `edits`. Of two edits that overlap, the one that starts first
    /// wins (the outer of two nested macro calls); the next pass finds what
    /// the other covered again. Insertions at one offset keep their order.
    pub fn apply(&self, mut edits: Vec<Edit>) -> SourceText {
        edits.sort_by_key(|edit| {
            (
                edit.start,
                edit.end != edit.start,
                std::cmp::Reverse(edit.end),
            )
        });
        let len = self.len();
        let mut out = Builder {
            text: String::with_capacity(self.text.len() + 256),
            origin: Vec::with_capacity(self.origin.len() + 256),
            marks: Vec::with_capacity(self.marks.len() + 256),
            uses: self.uses.clone(),
            files: self.files.clone(),
            descriptions: self.descriptions.clone(),
        };
        let mut cursor = 0u32;
        for edit in &edits {
            if edit.start < cursor || edit.end > len || edit.end < edit.start {
                continue;
            }
            self.copy_into(cursor, edit.start, &mut out);
            let mut use_id = self.use_of(&mut out, edit.start, edit.end, !edit.internal, None);
            for segment in &edit.segments {
                match segment {
                    Segment::Text(generated) => out.generate(generated, use_id, Mark::default()),
                    Segment::Code(code) => self.code_into(code, use_id, &mut out),
                    Segment::Copy(start, end) => self.copy_into(*start, *end, &mut out),
                    Segment::For(start, end, description) => {
                        use_id = self.use_of(
                            &mut out,
                            *start,
                            *end,
                            !edit.internal,
                            description.as_ref(),
                        );
                    }
                }
            }
            cursor = edit.end;
        }
        self.copy_into(cursor, len, &mut out);
        out.origin.push(self.origin(len));
        out.marks.push(Mark::default());
        let char_to_byte = char_offsets(&out.text);
        debug_assert_eq!(char_to_byte.len(), out.origin.len());
        debug_assert_eq!(char_to_byte.len(), out.marks.len());
        SourceText {
            text: out.text,
            char_to_byte,
            origin: out.origin,
            marks: out.marks,
            uses: out.uses,
            files: out.files,
            descriptions: out.descriptions,
            edited: true,
        }
    }

    /// The macro use that text put in place of `start..end` is generated
    /// for. Code generated inside generated code belongs to the use that
    /// generated the outer code: that is the one in the source.
    fn use_of(
        &self,
        out: &mut Builder,
        start: u32,
        end: u32,
        shown: bool,
        description: Option<&Arc<str>>,
    ) -> u32 {
        let description = description.map(|description| out.description_id(description));
        let inherited = self.marks[(start as usize).min(self.marks.len() - 1)].use_id;
        if inherited != 0 && start < self.len() {
            let outer = out.uses[inherited as usize - 1];
            return out.use_id(Use {
                shown,
                description: description.unwrap_or(outer.description),
                ..outer
            });
        }
        let use_start = self.origin(start);
        let use_end = if end > start {
            self.origin_end(end)
        } else {
            use_start
        };
        out.use_id(Use {
            start: use_start,
            end: use_end.max(use_start),
            shown,
            description: description.unwrap_or(0),
        })
    }

    fn copy_into(&self, start: u32, end: u32, out: &mut Builder) {
        if start >= end {
            return;
        }
        out.text.push_str(self.slice(start, end));
        out.origin
            .extend_from_slice(&self.origin[start as usize..end as usize]);
        out.marks
            .extend_from_slice(&self.marks[start as usize..end as usize]);
    }

    fn code_into(&self, code: &Code, use_id: u32, out: &mut Builder) {
        let chars = char_offsets(&code.text);
        let len = chars.len() as u32 - 1;
        let slice = |start: u32, end: u32| {
            &code.text[chars[start as usize] as usize..chars[end as usize] as usize]
        };
        let mut cursor = 0u32;
        for span in &code.spans {
            let end = span.start.saturating_add(span.len);
            if span.start < cursor || end > len {
                continue;
            }
            out.generate(slice(cursor, span.start), use_id, Mark::default());
            let text = slice(span.start, end);
            match &span.from {
                // The argument as the person wrote it: its characters keep
                // their place in the source.
                SpanSource::Text(at) if self.slice(*at, at + span.len) == text => {
                    self.copy_into(*at, at + span.len, out);
                }
                SpanSource::Text(_) => out.generate(text, use_id, Mark::default()),
                SpanSource::Quote { file, line, column } => {
                    let file = out.file_id(file);
                    out.generate(
                        text,
                        use_id,
                        Mark {
                            use_id,
                            file,
                            line: *line,
                            column: *column,
                        },
                    );
                }
            }
            cursor = end;
        }
        out.generate(slice(cursor, len), use_id, Mark::default());
    }
}

/// The text an [`SourceText::apply`] builds.
struct Builder {
    text: String,
    origin: Vec<u32>,
    marks: Vec<Mark>,
    uses: Vec<Use>,
    files: Vec<Arc<str>>,
    descriptions: Vec<Arc<str>>,
}

impl Builder {
    fn description_id(&mut self, description: &Arc<str>) -> u32 {
        if let Some(index) = self
            .descriptions
            .iter()
            .position(|known| known == description)
        {
            return index as u32 + 1;
        }
        self.descriptions.push(description.clone());
        self.descriptions.len() as u32
    }

    fn use_id(&mut self, used: Use) -> u32 {
        // A use is looked up among the latest: an edit and the ones after it.
        if let Some(index) = self.uses.iter().rposition(|known| *known == used) {
            return index as u32 + 1;
        }
        self.uses.push(used);
        self.uses.len() as u32
    }

    fn file_id(&mut self, file: &Arc<str>) -> u32 {
        if let Some(index) = self.files.iter().position(|known| known == file) {
            return index as u32 + 1;
        }
        self.files.push(file.clone());
        self.files.len() as u32
    }

    /// Add generated text. `first` is the mark of its first character when
    /// the text is from a quote: line and column advance from there.
    fn generate(&mut self, text: &str, use_id: u32, first: Mark) {
        if text.is_empty() {
            return;
        }
        let origin = self.uses[use_id as usize - 1].start;
        let mut mark = Mark { use_id, ..first };
        for ch in text.chars() {
            self.origin.push(origin);
            self.marks.push(mark);
            if mark.file != 0 {
                if ch == '\n' {
                    mark.line += 1;
                    mark.column = 0;
                } else {
                    mark.column += 1;
                }
            }
        }
        self.text.push_str(text);
    }
}

/// What the compilation of an expanded file keeps of the expansion.
#[derive(Debug)]
pub struct Expansion {
    /// The expanded text.
    pub text: SourceText,
    /// Per position of the parse, by index: its offset in the expanded
    /// text. The positions themselves point into the source as written.
    pub offsets: Vec<u32>,
}

/// Generated code a diagnostic is in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedCode {
    /// Its characters in the expanded text.
    pub start: u32,
    pub end: u32,
    /// What the code is, when it is more than the result of the macro use.
    pub description: Option<Arc<str>>,
    /// The part of a quote it was written in, when it is from one.
    pub quote: Option<QuoteRange>,
}

/// A range of a macro's file. Lines count from 1, columns from 0; `end` is
/// after the last character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuoteRange {
    pub file: Arc<str>,
    pub start: (u32, u32),
    pub end: (u32, u32),
}

impl Expansion {
    /// The generated code that a location with the positions `start` and
    /// `end` (by index) is in.
    pub fn generated_code(&self, start: u32, end: u32) -> Option<GeneratedCode> {
        let from = *self.offsets.get(start as usize)?;
        let to = *self.offsets.get(end as usize)?;
        self.text.generated_code(from, to)
    }
}

fn char_offsets(text: &str) -> Vec<u32> {
    let mut offsets: Vec<u32> = text.char_indices().map(|(byte, _)| byte as u32).collect();
    offsets.push(text.len() as u32);
    offsets
}

/// Line starts of a text, for turning an offset into a line and column.
pub struct LineTable {
    /// Character offset of the first character of each line.
    starts: Vec<u32>,
}

impl LineTable {
    pub fn new(text: &str) -> Self {
        let mut starts = vec![0u32];
        for (index, ch) in text.chars().enumerate() {
            if ch == '\n' {
                starts.push(index as u32 + 1);
            }
        }
        LineTable { starts }
    }

    /// The offset of the first character of the 1-based `line`.
    pub fn line_start(&self, line: u32) -> Option<u32> {
        self.starts.get((line as usize).checked_sub(1)?).copied()
    }

    /// The 1-based line of `offset` and the offset of that line's start.
    pub fn line_of(&self, offset: u32) -> (i32, u32) {
        let line = match self.starts.binary_search(&offset) {
            Ok(index) => index,
            Err(index) => index - 1,
        };
        (line as i32 + 1, self.starts[line])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replacement_keeps_origins_of_the_rest() {
        let source = SourceText::new("let a = %M.f(x)\nlet b = 2\n");
        let edited = source.apply(vec![Edit::replace(8, 15, "(x + 1)")]);
        assert_eq!(edited.text(), "let a = (x + 1)\nlet b = 2\n");
        // Generated characters point at the call.
        assert_eq!(edited.origin(8), 8);
        assert_eq!(edited.origin(12), 8);
        // What follows keeps its place in the original.
        assert_eq!(edited.origin(15), 15);
        assert_eq!(edited.slice(16, 21), "let b");
        assert_eq!(edited.origin(16), 16);
    }

    #[test]
    fn outer_edit_wins_and_insertions_keep_order() {
        let source = SourceText::new("abcdef");
        let edited = source.apply(vec![
            Edit::replace(2, 3, "X"),
            Edit::replace(1, 4, "Y"),
            Edit::insert(0, "1"),
            Edit::insert(0, "2"),
        ]);
        assert_eq!(edited.text(), "12aYef");
    }

    #[test]
    fn copies_keep_their_origin_inside_generated_text() {
        let source = SourceText::new("%code(a + ${b})");
        let edited = source.apply(vec![Edit::with(
            0,
            15,
            vec![
                Segment::Text("q([".into()),
                Segment::Copy(12, 13),
                Segment::Text("])".into()),
            ],
        )]);
        assert_eq!(edited.text(), "q([b])");
        assert_eq!(edited.origin(3), 12);
        assert_eq!(edited.origin(0), 0);
    }

    #[test]
    fn offsets_are_characters() {
        let source = SourceText::new("let s = \"é\" + %M.f(x)");
        let edited = source.apply(vec![Edit::replace(14, 21, "y")]);
        assert_eq!(edited.text(), "let s = \"é\" + y");
    }

    #[test]
    fn line_table() {
        let lines = LineTable::new("ab\ncd\n");
        assert_eq!(lines.line_of(0), (1, 0));
        assert_eq!(lines.line_of(3), (2, 3));
        assert_eq!(lines.line_of(4), (2, 3));
    }

    #[test]
    fn generated_text_knows_its_use_and_its_quote() {
        let source = SourceText::new("let a = %M.f(x + 1)\nlet b = 2\n");
        // The macro returned `{\n  (x + 1) * 2\n}`: the argument, in a quote.
        let code = Code {
            text: "{\n  (x + 1) * 2\n}".into(),
            spans: vec![
                Span {
                    start: 0,
                    len: 5,
                    from: SpanSource::Quote {
                        file: "M.res".into(),
                        line: 4,
                        column: 8,
                    },
                },
                Span {
                    start: 5,
                    len: 5,
                    from: SpanSource::Text(13),
                },
                Span {
                    start: 10,
                    len: 7,
                    from: SpanSource::Quote {
                        file: "M.res".into(),
                        line: 5,
                        column: 8,
                    },
                },
            ],
        };
        let edited = source.apply(vec![Edit::with(8, 19, vec![Segment::Code(code)])]);
        assert_eq!(edited.text(), "let a = {\n  (x + 1) * 2\n}\nlet b = 2\n");
        // The argument is the person's own text.
        assert_eq!(edited.slice(13, 18), "x + 1");
        assert_eq!(edited.origin(13), 13);
        assert_eq!(edited.generated(13), None);
        // The rest is generated for the whole use.
        let brace = edited.generated(8).unwrap();
        assert_eq!((brace.use_start, brace.use_end), (8, 19));
        assert_eq!(brace.quote, Some(("M.res".into(), 4, 8)));
        // After the newline in the quote: the next line, column 2.
        assert_eq!(
            edited.generated(12).unwrap().quote,
            Some(("M.res".into(), 5, 2))
        );
        assert_eq!(
            edited.generated(19).unwrap().quote,
            Some(("M.res".into(), 5, 9))
        );
        // A range that ends in generated text ends where the use ends.
        assert_eq!(edited.origin_end(22), 19);
        assert_eq!(edited.origin_end(4), 4);
        // What follows is the source as written.
        assert_eq!(edited.slice(26, 31), "let b");
        assert_eq!(edited.origin(26), 20);

        // Code generated inside generated code belongs to the outer use.
        let again = edited.apply(vec![Edit::replace(8, 9, "(")]);
        let inner = again.generated(8).unwrap();
        assert_eq!((inner.use_start, inner.use_end), (8, 19));
    }

    #[test]
    fn an_insertion_is_generated_for_the_use_it_names() {
        let source = SourceText::new("let j = Json.encode(alice)\n");
        let edited = source.apply(vec![Edit::with(
            0,
            0,
            vec![
                Segment::For(8, 19, Some("`Json.encode` for `user`".into())),
                Segment::Text("let rec f = 1\n".into()),
            ],
        )]);
        let function = edited.generated(4).unwrap();
        assert_eq!((function.use_start, function.use_end), (8, 19));
        assert_eq!(
            function.description.as_deref(),
            Some("`Json.encode` for `user`")
        );
        assert_eq!(edited.origin(4), 8);
        assert_eq!(edited.origin(14), 0);
    }
}
