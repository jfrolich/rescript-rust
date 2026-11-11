//! Source text with edits applied and a map back to the original.
//!
//! Macro expansion edits the source text of a file: a macro call is replaced
//! by the code the macro returned, a generated function is inserted before
//! the item that needs it. Every character of the edited text remembers the
//! offset it has in the file as written, so that diagnostics, source maps and
//! editor tooling keep pointing at what the person wrote. Generated text
//! takes the offset of the place it was generated for.
//!
//! Offsets are in characters, like `Position::cnum`.

/// One part of an edit's replacement.
#[derive(Debug, Clone)]
pub enum Segment {
    /// Generated text.
    Text(String),
    /// The characters `start..end` of the text being edited, kept with their
    /// origins.
    Copy(u32, u32),
}

/// Replace the characters `start..end` by `segments`. An insertion has
/// `start == end`.
#[derive(Debug, Clone)]
pub struct Edit {
    pub start: u32,
    pub end: u32,
    pub segments: Vec<Segment>,
}

impl Edit {
    pub fn replace(start: u32, end: u32, text: impl Into<String>) -> Self {
        Edit {
            start,
            end,
            segments: vec![Segment::Text(text.into())],
        }
    }

    pub fn insert(at: u32, text: impl Into<String>) -> Self {
        Edit::replace(at, at, text)
    }
}

/// A file's text during macro expansion.
#[derive(Debug, Clone)]
pub struct SourceText {
    text: String,
    /// Byte offset of each character, and of the end of the text.
    char_to_byte: Vec<u32>,
    /// Offset in the original text of each character, and of the end.
    origin: Vec<u32>,
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
        &self.text[self.char_to_byte[start as usize] as usize..self.char_to_byte[end as usize] as usize]
    }

    /// The offset in the original text of the character at `offset`.
    pub fn origin(&self, offset: u32) -> u32 {
        self.origin[(offset as usize).min(self.origin.len() - 1)]
    }

    /// Apply `edits`. Of two edits that overlap, the one that starts first
    /// wins (the outer of two nested macro calls); the next pass finds what
    /// the other covered again. Insertions at one offset keep their order.
    pub fn apply(&self, mut edits: Vec<Edit>) -> SourceText {
        edits.sort_by_key(|edit| (edit.start, edit.end != edit.start, std::cmp::Reverse(edit.end)));
        let len = self.len();
        let mut text = String::with_capacity(self.text.len() + 256);
        let mut origin = Vec::with_capacity(self.origin.len() + 256);
        let mut cursor = 0u32;
        for edit in &edits {
            if edit.start < cursor || edit.end > len || edit.end < edit.start {
                continue;
            }
            self.copy_into(cursor, edit.start, &mut text, &mut origin);
            let generated_origin = self.origin(edit.start);
            for segment in &edit.segments {
                match segment {
                    Segment::Text(generated) => {
                        text.push_str(generated);
                        origin.extend(generated.chars().map(|_| generated_origin));
                    }
                    Segment::Copy(start, end) => self.copy_into(*start, *end, &mut text, &mut origin),
                }
            }
            cursor = edit.end;
        }
        self.copy_into(cursor, len, &mut text, &mut origin);
        origin.push(self.origin(len));
        let char_to_byte = char_offsets(&text);
        debug_assert_eq!(char_to_byte.len(), origin.len());
        SourceText {
            text,
            char_to_byte,
            origin,
            edited: true,
        }
    }

    fn copy_into(&self, start: u32, end: u32, text: &mut String, origin: &mut Vec<u32>) {
        if start >= end {
            return;
        }
        text.push_str(self.slice(start, end));
        origin.extend_from_slice(&self.origin[start as usize..end as usize]);
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
        let edited = source.apply(vec![Edit {
            start: 0,
            end: 15,
            segments: vec![
                Segment::Text("q([".into()),
                Segment::Copy(12, 13),
                Segment::Text("])".into()),
            ],
        }]);
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
}
