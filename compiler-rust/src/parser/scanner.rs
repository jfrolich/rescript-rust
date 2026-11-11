//! Lexical scanner for ReScript source code.
//!
//! The scanner converts source text into a stream of tokens, handling:
//! - Identifiers and keywords
//! - Numeric literals (integers, floats, with various bases)
//! - String literals with escape sequences
//! - Comments (single-line, multi-line, doc comments)
//! - Template literals
//! - Regular expressions
//! - All operators and punctuation
//!
//! Uses direct byte-level scanning on &[u8] for performance:
//! - ASCII fast path (byte < 0x80) for all common token characters
//! - UTF-8 slow path only for non-ASCII characters (comments, strings)
//! - No upfront `Vec<char>` or `Vec<usize>` allocation

use std::borrow::Cow;
use std::fmt::Write as _;

use crate::intern::StrIdx;
use crate::location::Position;

use super::comment::{Comment, CommentStyle};
use super::diagnostics::{DiagnosticCategory, ParserDiagnostic};
use super::token::Token;
use super::utf8;

/// Special character value indicating end of file.
/// We use a value outside the valid char range.
const EOF_CHAR: char = '\u{FFFF}';

/// `Res_scanner.byte_order_mark`: the UTF-8 byte order mark that `src`
/// starts with, or "". The scanner skips it, and the formatter keeps it.
/// A Latin-1 decoded source holds the mark's three bytes as three chars.
pub fn byte_order_mark(src: &str) -> &str {
    const LATIN1_BOM: &str = "\u{EF}\u{BB}\u{BF}";
    const UTF8_BOM: &str = "\u{FEFF}";
    if src.starts_with(LATIN1_BOM) {
        &src[..LATIN1_BOM.len()]
    } else if src.starts_with(UTF8_BOM) {
        &src[..UTF8_BOM.len()]
    } else {
        ""
    }
}

/// A snapshot of scanner state for lookahead/restore.
#[derive(Debug, Clone)]
pub struct ScannerSnapshot {
    ch: char,
    offset: usize,
    ch_len: usize,
    char_pos: usize,
    offset16: usize,
    line_offset: usize,
    lnum: i32,
    diagnostics_len: usize,
}

/// The lexical scanner state.
#[derive(Debug)]
pub struct Scanner<'src> {
    /// Source filename (interned string index for sharing in marshal output).
    pub filename: StrIdx,
    /// Source code being scanned.
    src: &'src str,
    /// Source bytes for direct byte-level access.
    bytes: &'src [u8],
    /// Current character.
    ch: char,
    /// Byte length of current character in UTF-8.
    ch_len: usize,
    /// Current byte offset in source.
    offset: usize,
    /// Current character position (increments by 1 per char, like old char-index offset).
    /// Used for line_offset and position tracking to preserve OCaml parity.
    char_pos: usize,
    /// UTF-16 code units since line start (for OCaml-compatible column counting).
    offset16: usize,
    /// Character position of current line start (char-indexed, not byte-indexed).
    /// This preserves OCaml parity where line_offset is a character position.
    line_offset: usize,
    /// Current line number (1-indexed).
    lnum: i32,
    /// Collected diagnostics.
    diagnostics: Vec<ParserDiagnostic>,
    /// Byte offset of the first LF skipped between tokens since the last
    /// `take_line_break` (res_scanner.ml `line_break`). Literals and
    /// comments consume their own line breaks.
    line_break: Option<usize>,
}

/// Result of scanning a token.
#[derive(Debug, Clone)]
pub struct ScanResult<'src> {
    /// Start position of the token.
    pub start_pos: Position,
    /// End position of the token.
    pub end_pos: Position,
    /// The scanned token.
    pub token: Token<'src>,
}

impl<'src> Scanner<'src> {
    /// Create a new scanner for the given source.
    /// filename should be an interned StrIdx from the arena.
    pub fn new(filename: StrIdx, src: &'src str) -> Self {
        let bytes = src.as_bytes();
        // res_scanner.ml:152-167: skip a byte order mark: it is not part of
        // the program, and the first line starts after it, as in an editor.
        let bom = byte_order_mark(src);
        let offset = bom.len();
        let char_pos = bom.chars().count();
        let (ch, ch_len) = if offset >= bytes.len() {
            (EOF_CHAR, 0)
        } else if bytes[offset] < 0x80 {
            (bytes[offset] as char, 1)
        } else {
            let (cp, len) = utf8::decode_codepoint(bytes, offset);
            (char::from_u32(cp as u32).unwrap_or(EOF_CHAR), len)
        };

        Self {
            filename,
            src,
            bytes,
            ch,
            ch_len,
            offset,
            char_pos,
            offset16: 0,
            line_offset: char_pos,
            lnum: 1,
            diagnostics: Vec::new(),
            line_break: None,
        }
    }

    /// The first LF skipped between tokens since the previous call, and
    /// forget it (res_parser.ml `read`).
    pub fn take_line_break(&mut self) -> Option<usize> {
        self.line_break.take()
    }

    /// Get collected diagnostics.
    pub fn diagnostics(&self) -> &[ParserDiagnostic] {
        &self.diagnostics
    }

    /// Take collected diagnostics, leaving an empty vec.
    pub fn take_diagnostics(&mut self) -> Vec<ParserDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// res_scanner.ml `scan_binary_operator`: extend a just-scanned `<` or
    /// `>` with an immediately adjacent operator suffix, without skipping
    /// trivia. Returns the token unchanged (and does not advance) when there
    /// is no suffix.
    pub fn scan_binary_operator(&mut self, token: &Token<'src>) -> Option<Token<'src>> {
        match (token, self.ch) {
            (Token::LessThan, '<') => {
                self.next();
                Some(Token::LeftShift)
            }
            (Token::GreaterThan, '=') => {
                self.next();
                Some(Token::GreaterEqual)
            }
            (Token::GreaterThan, '>') => {
                self.next();
                if self.ch == '>' {
                    self.next();
                    Some(Token::RightShiftUnsigned)
                } else {
                    Some(Token::RightShift)
                }
            }
            _ => None,
        }
    }

    /// Create a snapshot of the scanner state for lookahead.
    pub fn snapshot(&self) -> ScannerSnapshot {
        ScannerSnapshot {
            ch: self.ch,
            offset: self.offset,
            ch_len: self.ch_len,
            char_pos: self.char_pos,
            offset16: self.offset16,
            line_offset: self.line_offset,
            lnum: self.lnum,
            diagnostics_len: self.diagnostics.len(),
        }
    }

    /// Restore scanner state from a snapshot.
    pub fn restore(&mut self, snapshot: ScannerSnapshot) {
        self.ch = snapshot.ch;
        self.offset = snapshot.offset;
        self.ch_len = snapshot.ch_len;
        self.char_pos = snapshot.char_pos;
        self.offset16 = snapshot.offset16;
        self.line_offset = snapshot.line_offset;
        self.lnum = snapshot.lnum;
        self.diagnostics.truncate(snapshot.diagnostics_len);
    }

    /// Get a reference to the source string.
    pub fn src(&self) -> &str {
        self.src
    }

    /// Get the current position.
    ///
    /// For OCaml parity, we use `line_offset + offset16` for cnum.
    /// This matches OCaml where `pos_cnum = scanner.line_offset + scanner.offset16`,
    /// giving us UTF-16 code unit counting for columns.
    /// `line_offset` and `char_pos` are character-indexed (not byte-indexed),
    /// as OCaml's are, so error locations match.
    pub fn position(&self) -> Position {
        Position::new(
            self.filename,
            self.lnum,
            self.line_offset as i32,
            (self.line_offset + self.offset16) as i32, // UTF-16 code unit position
        )
    }

    /// Report an error at the given positions.
    fn error(&mut self, start_pos: Position, end_pos: Position, category: DiagnosticCategory) {
        self.diagnostics
            .push(ParserDiagnostic::new(start_pos, end_pos, category));
    }

    /// Decode the character at the given byte offset.
    #[inline]
    fn decode_at(&self, byte_offset: usize) -> (char, usize) {
        if byte_offset >= self.bytes.len() {
            return (EOF_CHAR, 0);
        }
        let b = self.bytes[byte_offset];
        if b < 0x80 {
            (b as char, 1)
        } else {
            let (cp, len) = utf8::decode_codepoint(self.bytes, byte_offset);
            (char::from_u32(cp as u32).unwrap_or(EOF_CHAR), len)
        }
    }

    /// Advance to the next character.
    ///
    /// Operates directly on the byte array. For ASCII bytes (< 0x80), this is a single
    /// byte advance. For multi-byte UTF-8 sequences, advances by the character's byte width.
    ///
    /// We track offset16 (UTF-16 code units since line start) for OCaml-compatible
    /// column counting.
    fn next(&mut self) {
        if self.offset >= self.bytes.len() {
            self.ch = EOF_CHAR;
            self.ch_len = 0;
            return;
        }

        let next_char_pos = self.char_pos + 1;

        // OCaml `Res_scanner.next`: a continuation byte adds no UTF-16 code
        // unit, ASCII adds one, and a leading byte adds two only when it starts
        // a valid UTF-8 sequence for a code point above U+FFFF. The source is
        // Latin-1 decoded (one char per original byte).
        let byte = self.ch as u32;
        let utf16len = if byte & 0xc0 == 0x80 {
            0
        } else if byte < 0x80 {
            1
        } else if byte > 0xff {
            // Source that was not Latin-1 decoded holds whole code points.
            self.ch.len_utf16()
        } else {
            let mut bytes = [0u8; 4];
            let mut count = 0;
            for ch in self.src[self.offset..].chars().take(4) {
                if ch as u32 > 0xff {
                    break;
                }
                bytes[count] = ch as u32 as u8;
                count += 1;
            }
            match crate::string_literal::get_utf_8_uchar(&bytes[..count], 0) {
                (true, codepoint, _) if codepoint > 0xffff => 2,
                _ => 1,
            }
        };

        // res_scanner.ml:88-97: a line ends at LF, or at a CR not followed by
        // LF. CRLF ends a line once, at its LF.
        let newline = match self.ch {
            '\n' => true,
            '\r' => self.bytes.get(self.offset + self.ch_len) != Some(&b'\n'),
            _ => false,
        };
        if newline {
            self.line_offset = next_char_pos;
            self.offset16 = 0;
            self.lnum += 1;
        } else {
            self.offset16 += utf16len;
        }

        // Advance byte offset by current character's byte width
        let next_byte_offset = self.offset + self.ch_len;
        self.offset = next_byte_offset;
        self.char_pos = next_char_pos;

        // Decode next character
        let (ch, ch_len) = self.decode_at(next_byte_offset);
        self.ch = ch;
        self.ch_len = ch_len;
        // res_scanner.ml:111-114: at EOF the column becomes the byte count
        // since the line start (`offset16 <- offset - line_offset`).
        if next_byte_offset >= self.bytes.len() {
            self.offset16 = self.char_pos - self.line_offset;
        }
    }

    /// Advance by 2 characters.
    fn next2(&mut self) {
        self.next();
        self.next();
    }

    /// Advance by 3 characters.
    fn next3(&mut self) {
        self.next();
        self.next();
        self.next();
    }

    /// OCaml `Scanner.peek_slash` (res_scanner.ml:140-151): whether the next
    /// non-whitespace source character after the current token is `/`.
    pub fn peek_slash(&self) -> bool {
        let mut offset = self.offset;
        while offset < self.bytes.len() {
            match self.bytes[offset] {
                b' ' | b'\t' | b'\n' | b'\r' => offset += 1,
                c => return c == b'/',
            }
        }
        false
    }

    /// Byte offset reached by skipping `n` characters from `byte_offset`
    /// (stops at EOF).
    fn skip_chars_from(&self, mut byte_offset: usize, n: usize) -> usize {
        for _ in 0..n {
            byte_offset += self.decode_at(byte_offset).1;
        }
        byte_offset
    }

    /// Peek at the character `n + 1` positions ahead without advancing.
    fn peek_nth(&self, n: usize) -> char {
        let off = self.skip_chars_from(self.offset + self.ch_len, n);
        self.decode_at(off).0
    }

    /// Peek at the next character without advancing.
    fn peek(&self) -> char {
        self.peek_nth(0)
    }

    /// Peek at the character 2 positions ahead.
    fn peek2(&self) -> char {
        self.peek_nth(1)
    }

    /// Peek at the character 3 positions ahead.
    fn peek3(&self) -> char {
        self.peek_nth(2)
    }

    /// Check if a character is whitespace.
    fn is_whitespace(ch: char) -> bool {
        matches!(ch, ' ' | '\t' | '\n' | '\r')
    }

    /// Skip whitespace characters.
    fn skip_whitespace(&mut self) {
        while Self::is_whitespace(self.ch) {
            if self.ch == '\n' && self.line_break.is_none() {
                self.line_break = Some(self.offset);
            }
            self.next();
        }
    }

    /// Get the digit value of a character (0-15 for hex, 16+ for invalid).
    fn digit_value(ch: char) -> u32 {
        match ch {
            '0'..='9' => ch as u32 - '0' as u32,
            'a'..='f' => ch as u32 - 'a' as u32 + 10,
            'A'..='F' => ch as u32 - 'A' as u32 + 10,
            _ => 16,
        }
    }

    /// Extract a substring from the source using byte offsets.
    ///
    /// In byte-level scanning mode, start and end are byte offsets directly,
    /// so this is a simple slice operation.
    fn substring(&self, start: usize, end: usize) -> &'src str {
        let start = start.min(self.src.len());
        let end = end.min(self.src.len());
        &self.src[start..end]
    }

    /// Decode a UTF-8 codepoint from the scanner's Latin-1 source view.
    ///
    /// Source files are loaded as "one byte -> one char", so each source char
    /// stores an original byte value in its low 8 bits. Reconstruct those bytes
    /// before calling UTF-8 decode, matching OCaml scanner behavior.
    fn decode_codepoint_from_latin1_source(&self, start: usize) -> (i32, usize) {
        let Some(tail) = self.src.get(start..) else {
            return (utf8::REPLACEMENT_CHAR, 1);
        };
        let mut raw = [0u8; 6];
        let mut len = 0usize;
        for ch in tail.chars().take(raw.len()) {
            raw[len] = ch as u8;
            len += 1;
        }
        if len == 0 {
            (utf8::REPLACEMENT_CHAR, 1)
        } else {
            utf8::decode_codepoint(&raw[..len], 0)
        }
    }

    /// Extract `char_len` source characters from `start`, preserving the scanner's
    /// Latin-1 byte view used by codepoint literals.
    fn substring_latin1_chars(&self, start: usize, char_len: usize) -> String {
        self.src
            .get(start..)
            .map(|s| s.chars().take(char_len).collect())
            .unwrap_or_default()
    }

    /// Scan an identifier or keyword.
    fn scan_identifier(&mut self) -> Token<'src> {
        let start_off = self.offset;

        // Skip valid identifier characters (all ASCII, so byte == char)
        while matches!(self.ch, 'A'..='Z' | 'a'..='z' | '0'..='9' | '_' | '\'' | '$') {
            self.next();
        }

        let ident = self.substring(start_off, self.offset);

        // Check for special cases: list{, dict{, let?
        match (self.ch, ident) {
            ('{', "list") => {
                self.next();
                Token::List
            }
            ('{', "dict") => {
                self.next();
                Token::Dict
            }
            ('?', "let") => {
                self.next();
                Token::Let { unwrap: true }
            }
            _ => Token::lookup_keyword(ident),
        }
    }

    /// Scan digits in the given base.
    fn scan_digits(&mut self, base: u32) -> bool {
        let mut found_digits = false;

        if base <= 10 {
            loop {
                match self.ch {
                    '0'..='9' => {
                        self.next();
                        found_digits = true;
                    }
                    '_' => {
                        self.next();
                    }
                    _ => break,
                }
            }
        } else {
            // Hex
            loop {
                match self.ch {
                    '0'..='9' | 'a'..='f' | 'A'..='F' => {
                        self.next();
                        found_digits = true;
                    }
                    '_' => {
                        self.next();
                    }
                    _ => break,
                }
            }
        }

        found_digits
    }

    /// Scan a number literal.
    fn scan_number(&mut self) -> Token<'src> {
        let start_off = self.offset;

        // Determine base
        let base = if self.ch == '0' {
            match self.peek() {
                'x' | 'X' => {
                    self.next2();
                    16
                }
                'o' | 'O' => {
                    self.next2();
                    8
                }
                'b' | 'B' => {
                    self.next2();
                    2
                }
                _ => {
                    self.next();
                    8
                }
            }
        } else {
            10
        };

        self.scan_digits(base);

        // Decimal part
        let mut is_float = false;
        if self.ch == '.' {
            self.next();
            self.scan_digits(base);
            is_float = true;
        }

        // Exponent part
        match self.ch {
            'e' | 'E' | 'p' | 'P' => {
                let start_pos = self.position();
                match self.peek() {
                    '+' | '-' => self.next2(),
                    _ => self.next(),
                }
                let end_pos = self.position();
                if !self.scan_digits(base) {
                    self.error(
                        start_pos,
                        end_pos,
                        DiagnosticCategory::message("Expected digits after exponential notation."),
                    );
                }
                is_float = true;
            }
            _ => {}
        }

        let literal = Cow::Borrowed(self.substring(start_off, self.offset));

        // Suffix
        let suffix = match self.ch {
            'g'..='z' | 'G'..='Z' => {
                let s = self.ch;
                self.next();
                Some(s)
            }
            _ => None,
        };

        if is_float {
            Token::Float { f: literal, suffix }
        } else {
            Token::Int { i: literal, suffix }
        }
    }

    /// Scan a string literal.
    fn scan_string(&mut self) -> Token<'src> {
        let start_pos = self.position();
        self.next(); // consume opening quote

        // OCaml keeps escape sequences as text, only converting decimal to hex.
        // Literals without escapes borrow from the source; the buffer is only
        // allocated at the first escape, after which text is copied verbatim
        // except for decimal escapes which get converted to hex format.
        let mut result: Option<String> = None;
        let mut chunk_start = self.offset;

        loop {
            match self.ch {
                '"' => {
                    let chunk = self.substring(chunk_start, self.offset);
                    let token = match result {
                        None => Token::String(Cow::Borrowed(chunk)),
                        Some(mut buf) => {
                            buf.push_str(chunk);
                            Token::String(Cow::Owned(buf))
                        }
                    };
                    self.next();
                    return token;
                }
                '\\' => {
                    // Add content before the escape (including the backslash)
                    let buf = result.get_or_insert_with(String::new);
                    buf.push_str(self.substring(chunk_start, self.offset));
                    buf.push('\\');
                    let escape_start_pos = self.position();
                    self.next(); // consume backslash

                    // Check if this is a decimal escape that needs conversion
                    let escape_start = self.offset;
                    self.scan_string_escape_sequence_text(&escape_start_pos);
                    let escape_end = self.offset;

                    // Check if it was a 3-digit decimal escape
                    let escape_text = self.substring(escape_start, escape_end);
                    let buf = result.as_mut().expect("buffer allocated above");
                    match escape_text.parse::<u32>() {
                        Ok(value)
                            if value <= 255
                                && escape_text.len() == 3
                                && escape_text.chars().all(|c| c.is_ascii_digit()) =>
                        {
                            // Convert decimal to hex format
                            write!(buf, "x{:02x}", value).expect("writing to a String");
                        }
                        // Keep other escapes (and invalid values) as-is
                        _ => buf.push_str(escape_text),
                    }
                    chunk_start = self.offset;
                }
                c if c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(start_pos, end_pos, DiagnosticCategory::unclosed_string());
                    let chunk = self.substring(chunk_start, self.offset);
                    return Token::String(match result {
                        None => Cow::Borrowed(chunk),
                        Some(mut buf) => {
                            buf.push_str(chunk);
                            Cow::Owned(buf)
                        }
                    });
                }
                _ => self.next(),
            }
        }
    }

    /// Scan past a string escape sequence, advancing the scanner position.
    /// This doesn't interpret the escape, just skips past it.
    fn scan_string_escape_sequence_text(&mut self, start_pos: &Position) {
        match self.ch {
            'n' | 't' | 'b' | 'r' | '\\' | ' ' | '\'' | '"' => {
                self.next();
            }
            '0' if !self.peek().is_ascii_digit() => {
                // \0 when not followed by digit
                self.next();
            }
            '0'..='9' => {
                // Decimal escape \NNN, exactly three digits.
                self.scan_string_escape_digits_max(start_pos, 3, 10, 255);
            }
            'x' => {
                // Hex escape \xNN
                self.next();
                self.scan_string_escape_digits_max(start_pos, 2, 16, 255);
            }
            'u' => {
                self.next();
                if self.ch == '{' {
                    // Unicode escape \u{NNNN}: one or more hex digits.
                    self.next();
                    let max = 0x10FFFF;
                    let mut x: u32 = 0;
                    let mut has_digit = false;
                    while let Some(digit) = self.ch.to_digit(16) {
                        has_digit = true;
                        x = if x > (max - digit) / 16 {
                            max + 1
                        } else {
                            x * 16 + digit
                        };
                        self.next();
                    }
                    if self.ch == '}' {
                        if !has_digit || x > max || (0xD800..0xE000).contains(&x) {
                            self.invalid_unicode_code_point(start_pos);
                        }
                        self.next();
                    } else {
                        self.invalid_unicode_code_point(start_pos);
                    }
                } else {
                    // Unicode escape \uNNNN, exactly four hex digits; a high
                    // surrogate must be followed by a low-surrogate escape.
                    let high = self.scan_string_escape_digits(start_pos, 4, 16);
                    if (0xD800..=0xDBFF).contains(&high) {
                        if self.ch == '\\' && self.peek() == 'u' {
                            self.next();
                            self.next();
                            let low = self.scan_string_escape_digits(start_pos, 4, 16);
                            if low >= 0 && !(0xDC00..=0xDFFF).contains(&low) {
                                self.invalid_unicode_code_point(start_pos);
                            }
                        } else {
                            self.invalid_unicode_code_point(start_pos);
                        }
                    } else if high > 0x10FFFF || (0xDC00..=0xDFFF).contains(&high) {
                        self.invalid_unicode_code_point(start_pos);
                    }
                }
            }
            _ => {
                // OCaml `scan_string_escape_sequence` (res_scanner.ml:405-416):
                // an unknown escape, or the end of input, is left to the
                // string loop without a diagnostic.
            }
        }
    }

    /// OCaml `scan_digits` in `scan_string_escape_sequence`: returns -1 after
    /// reporting a non-digit.
    fn scan_string_escape_digits(&mut self, start_pos: &Position, digits: usize, base: u32) -> i64 {
        let mut value: i64 = 0;
        for _ in 0..digits {
            let Some(digit) = self.ch.to_digit(base) else {
                let end_pos = self.position();
                let message = if self.ch == EOF_CHAR {
                    "unclosed escape sequence"
                } else {
                    "unknown escape sequence"
                };
                self.error(*start_pos, end_pos, DiagnosticCategory::message(message));
                return -1;
            };
            self.next();
            value = (value * base as i64) + digit as i64;
        }
        value
    }

    fn scan_string_escape_digits_max(
        &mut self,
        start_pos: &Position,
        digits: usize,
        base: u32,
        max: i64,
    ) {
        let value = self.scan_string_escape_digits(start_pos, digits, base);
        if value > max || (0xD800..0xE000).contains(&value) {
            self.invalid_unicode_code_point(start_pos);
        }
    }

    fn invalid_unicode_code_point(&mut self, start_pos: &Position) {
        let end_pos = self.position();
        self.error(
            *start_pos,
            end_pos,
            DiagnosticCategory::message("escape sequence is invalid unicode code point"),
        );
    }

    /// Scan a single-line comment.
    fn scan_single_line_comment(&mut self) -> Token<'src> {
        let start_off = self.offset;
        let start_pos = self.position();

        // Skip to end of line
        while !matches!(self.ch, '\n' | '\r') && self.ch != EOF_CHAR {
            self.next();
        }

        let end_pos = self.position();
        let content = self.substring(start_off, self.offset).to_string();

        Token::Comment(Comment {
            txt: content,
            style: CommentStyle::SingleLine,
            loc: crate::location::Location::from_positions(start_pos, end_pos),
            prev_tok_end_pos: Position::default(),
            prev_tok_is_question: false,
            jsx_container: None,
        })
    }

    /// Scan a multi-line comment.
    fn scan_multi_line_comment(&mut self) -> Token<'src> {
        let doc_comment = self.peek2() == '*' && self.peek3() != '/';
        let standalone = doc_comment && self.peek3() == '*';

        // Calculate content start: skip the comment opener (/*,  /**, /***)
        // We need to compute byte offsets for the content
        let content_char_skip = if doc_comment {
            if standalone { 4 } else { 3 }
        } else {
            2
        };

        // Compute byte offset for content start by skipping N characters from current offset
        let content_start_off = self.skip_chars_from(self.offset, content_char_skip);

        let start_pos = self.position();
        let mut depth = 0;

        loop {
            match (self.ch, self.peek()) {
                ('/', '*') => {
                    self.next2();
                    depth += 1;
                }
                ('*', '/') => {
                    self.next2();
                    if depth > 1 {
                        depth -= 1;
                    } else {
                        break;
                    }
                }
                (c, _) if c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(start_pos, end_pos, DiagnosticCategory::unclosed_comment());
                    break;
                }
                _ => self.next(),
            }
        }

        // Content ends 2 bytes before current position (before closing */)
        // But we need to compute this in byte offsets
        // OCaml `scanner.offset - 2`: two source bytes back, i.e. two chars
        // of the Latin-1 source view (each possibly two UTF-8 bytes here, when
        // an unclosed comment ends at EOF on non-ASCII text).
        let content_end_off = self.src[..self.offset.min(self.src.len())]
            .char_indices()
            .rev()
            .nth(1)
            .map_or(0, |(idx, _)| idx);

        let content: Cow<'src, str> =
            if content_start_off <= content_end_off && content_start_off < self.src.len() {
                Cow::Borrowed(self.substring(content_start_off, content_end_off))
            } else {
                Cow::Borrowed("")
            };

        let end_pos = self.position();
        let loc = crate::location::Location::from_positions(start_pos, end_pos);

        if doc_comment {
            // OCaml `Res_parser.comment_text_for_attribute`: invalid UTF-8 in
            // a doc or module comment is reported and replaced by U+FFFD.
            let content = if crate::string_literal::is_valid_utf8(&content) {
                content
            } else {
                self.error(
                    loc.loc_start,
                    loc.loc_end,
                    DiagnosticCategory::message("Invalid code point"),
                );
                Cow::Owned(crate::string_literal::replace_invalid_utf8(&content))
            };
            if standalone {
                Token::ModuleComment { loc, content }
            } else {
                Token::DocComment { loc, content }
            }
        } else {
            Token::Comment(Comment {
                txt: content.into_owned(),
                style: CommentStyle::MultiLine,
                loc,
                prev_tok_end_pos: Position::default(),
                prev_tok_is_question: false,
                jsx_container: None,
            })
        }
    }

    /// Scan a template literal token.
    pub fn scan_template_literal_token(&mut self) -> ScanResult<'src> {
        let start_off = self.offset;

        let start_pos = self.position();

        loop {
            let last_pos = self.position();
            match self.ch {
                '`' => {
                    self.next();
                    // backtick is 1 byte, so offset - 1 is correct
                    let contents = Cow::Borrowed(self.substring(start_off, self.offset - 1));
                    let end_pos = self.position();
                    return ScanResult {
                        start_pos,
                        end_pos,
                        token: Token::TemplateTail {
                            text: contents,
                            pos: last_pos,
                        },
                    };
                }
                '$' if self.peek() == '{' => {
                    self.next2();
                    // ${ is 2 bytes, so offset - 2 is correct
                    let contents = Cow::Borrowed(self.substring(start_off, self.offset - 2));
                    let end_pos = self.position();
                    return ScanResult {
                        start_pos,
                        end_pos,
                        token: Token::TemplatePart {
                            text: contents,
                            pos: last_pos,
                        },
                    };
                }
                '\\' => {
                    // Escape sequences in template literals
                    match self.peek() {
                        '`' | '\\' | '$' | '\n' | '\r' => self.next2(),
                        _ => self.next(),
                    }
                }
                c if c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(start_pos, end_pos, DiagnosticCategory::unclosed_template());
                    // OCaml uses (max (scanner.offset - 1 - start_off) 0) to exclude the last char
                    let end_off = if self.offset > start_off {
                        // OCaml drops the last source byte, which is the last
                        // char of the Latin-1 source view (one char per byte,
                        // possibly two bytes in the Rust string).
                        let prev_len = self.src[..self.offset.min(self.src.len())]
                            .chars()
                            .next_back()
                            .map_or(1, char::len_utf8);
                        self.offset.saturating_sub(prev_len).max(start_off)
                    } else {
                        start_off
                    };
                    let contents = Cow::Borrowed(self.substring(start_off, end_off));
                    return ScanResult {
                        start_pos,
                        end_pos,
                        token: Token::TemplateTail {
                            text: contents,
                            pos: last_pos,
                        },
                    };
                }
                _ => self.next(),
            }
        }
    }

    /// Scan the next token.
    pub fn scan(&mut self) -> ScanResult<'src> {
        // Start of the first unknown character skipped by this call, if any.
        let mut recovery_start_pos: Option<Position> = None;
        loop {
            self.skip_whitespace();
            let start_pos = self.position();

            let token = match self.ch {
                // Identifiers and keywords
                'A'..='Z' | 'a'..='z' | '$' => self.scan_identifier(),

                // Numbers
                '0'..='9' => self.scan_number(),

                // Template literal
                '`' => {
                    self.next();
                    Token::Backtick
                }

                // Operators and punctuation
                '~' => {
                    if self.peek() == '~' && self.peek2() == '~' {
                        self.next3();
                        Token::Bnot
                    } else {
                        self.next();
                        Token::Tilde
                    }
                }
                '?' => {
                    self.next();
                    Token::Question
                }
                ';' => {
                    self.next();
                    Token::Semicolon
                }
                '(' => {
                    self.next();
                    Token::Lparen
                }
                ')' => {
                    self.next();
                    Token::Rparen
                }
                '[' => {
                    self.next();
                    Token::Lbracket
                }
                ']' => {
                    self.next();
                    Token::Rbracket
                }
                '{' => {
                    self.next();
                    Token::Lbrace
                }
                '}' => {
                    self.next();
                    Token::Rbrace
                }
                ',' => {
                    self.next();
                    Token::Comma
                }
                '"' => self.scan_string(),

                '_' => {
                    if matches!(self.peek(), 'A'..='Z' | 'a'..='z' | '0'..='9' | '_' | '$') {
                        self.scan_identifier()
                    } else {
                        self.next();
                        Token::Underscore
                    }
                }

                '#' => {
                    if self.peek() == '=' {
                        self.next2();
                        Token::HashEqual
                    } else {
                        self.next();
                        Token::Hash
                    }
                }

                '*' => match self.peek() {
                    '*' => {
                        self.next2();
                        Token::Exponentiation
                    }
                    '.' => {
                        self.next2();
                        Token::AsteriskDot
                    }
                    _ => {
                        self.next();
                        Token::Asterisk
                    }
                },

                '@' => {
                    if self.peek() == '@' {
                        self.next2();
                        Token::AtAt
                    } else {
                        self.next();
                        Token::At
                    }
                }

                '%' => {
                    if self.peek() == '%' {
                        self.next2();
                        Token::PercentPercent
                    } else {
                        self.next();
                        Token::Percent
                    }
                }

                '|' => match (self.peek(), self.peek2()) {
                    ('|', '|') => {
                        self.next3();
                        Token::Bor
                    }
                    ('|', _) => {
                        self.next2();
                        Token::Lor
                    }
                    _ => {
                        self.next();
                        Token::Bar
                    }
                },

                '&' => match (self.peek(), self.peek2()) {
                    ('&', '&') => {
                        self.next3();
                        Token::Band
                    }
                    ('&', _) => {
                        self.next2();
                        Token::Land
                    }
                    _ => {
                        self.next();
                        Token::Ampersand
                    }
                },

                '^' => {
                    if self.peek() == '^' && self.peek2() == '^' {
                        self.next3();
                        Token::Bxor
                    } else {
                        self.next();
                        Token::Caret
                    }
                }

                ':' => match self.peek() {
                    '=' => {
                        self.next2();
                        Token::ColonEqual
                    }
                    '>' => {
                        self.next2();
                        Token::ColonGreaterThan
                    }
                    _ => {
                        self.next();
                        Token::Colon
                    }
                },

                '/' => match self.peek() {
                    '/' => {
                        self.next2();
                        self.scan_single_line_comment()
                    }
                    '*' => self.scan_multi_line_comment(),
                    _ => {
                        // OCaml's scanner always yields `/` or `/.`; the parser rescans
                        // a regex literal with `next_regex_token` in expression position.
                        if self.peek() == '.' {
                            self.next2();
                            Token::ForwardslashDot
                        } else {
                            self.next();
                            Token::Forwardslash
                        }
                    }
                },

                '-' => match self.peek() {
                    '.' => {
                        self.next2();
                        Token::MinusDot
                    }
                    '>' => {
                        self.next2();
                        Token::MinusGreater
                    }
                    _ => {
                        self.next();
                        Token::Minus
                    }
                },

                '+' => match self.peek() {
                    '.' => {
                        self.next2();
                        Token::PlusDot
                    }
                    '+' => {
                        self.next2();
                        Token::PlusPlus
                    }
                    '=' => {
                        self.next2();
                        Token::PlusEqual
                    }
                    _ => {
                        self.next();
                        Token::Plus
                    }
                },

                '>' => {
                    self.next();
                    Token::GreaterThan
                }

                '<' => match self.peek() {
                    '=' => {
                        self.next2();
                        Token::LessEqual
                    }
                    _ => {
                        self.next();
                        Token::LessThan
                    }
                },

                '.' => match (self.peek(), self.peek2()) {
                    ('.', '.') => {
                        self.next3();
                        Token::DotDotDot
                    }
                    ('.', _) => {
                        self.next2();
                        Token::DotDot
                    }
                    _ => {
                        self.next();
                        Token::Dot
                    }
                },

                '\'' => match (self.peek(), self.peek2()) {
                    ('\\', '"') => {
                        self.next();
                        Token::SingleQuote
                    }
                    ('\\', _) => {
                        self.next2();
                        self.scan_escape()
                    }
                    (ch, '\'') => {
                        // Save the byte offset of the character between quotes
                        let char_byte_off = self.offset + self.ch_len; // offset of the char after '
                        self.next3();
                        // The character is 1 byte (ASCII) since we matched it against a char pattern
                        let original = Cow::Borrowed(
                            self.substring(char_byte_off, char_byte_off + ch.len_utf8()),
                        );
                        Token::Codepoint {
                            c: ch as i32,
                            original,
                        }
                    }
                    _ => {
                        // Match OCaml res_scanner.ml: try decoding a UTF-8 codepoint literal
                        // after the opening quote, then fall back to SingleQuote on failure.
                        let ch = self.peek();
                        self.next();
                        let offset = self.offset;
                        let offset16 = self.offset16;
                        let char_pos = self.char_pos;
                        let ch_len = self.ch_len;
                        let (codepoint, length) =
                            self.decode_codepoint_from_latin1_source(self.offset);

                        for _ in 0..length {
                            self.next();
                        }

                        if self.ch == '\'' {
                            let contents = self.substring_latin1_chars(offset, length);
                            self.next();
                            Token::Codepoint {
                                c: codepoint,
                                original: contents.into(),
                            }
                        } else {
                            self.ch = ch;
                            self.offset = offset;
                            self.offset16 = offset16;
                            self.char_pos = char_pos;
                            self.ch_len = ch_len;
                            Token::SingleQuote
                        }
                    }
                },

                '!' => match (self.peek(), self.peek2()) {
                    ('=', '=') => {
                        self.next3();
                        Token::BangEqualEqual
                    }
                    ('=', _) => {
                        self.next2();
                        Token::BangEqual
                    }
                    _ => {
                        self.next();
                        Token::Bang
                    }
                },

                '=' => match (self.peek(), self.peek2()) {
                    ('=', '=') => {
                        self.next3();
                        Token::EqualEqualEqual
                    }
                    ('=', _) => {
                        self.next2();
                        Token::EqualEqual
                    }
                    ('>', _) => {
                        self.next2();
                        Token::EqualGreater
                    }
                    _ => {
                        self.next();
                        Token::Equal
                    }
                },

                '\\' => {
                    let start_pos = self.position();
                    self.scan_exotic_identifier(start_pos)
                }

                c if c == EOF_CHAR => {
                    self.next();
                    Token::Eof
                }

                ch => {
                    // Unknown character
                    self.next();
                    let end_pos = self.position();
                    self.error(start_pos, end_pos, DiagnosticCategory::unknown_uchar(ch));
                    // OCaml: `let _, _, token = scan scanner in (start_pos, end_pos, token)`
                    // keeps the outer start_pos. Loop instead of recursing so a long
                    // run of unknown characters cannot overflow the stack.
                    recovery_start_pos.get_or_insert(start_pos);
                    continue;
                }
            };

            let end_pos = self.position();
            return ScanResult {
                start_pos: recovery_start_pos.unwrap_or(start_pos),
                end_pos,
                token,
            };
        }
    }

    /// Scan a regex literal from the current position (after the opening `/` has been consumed).
    /// This matches OCaml's `scan_regex` which is called by the parser when it encounters a `/`
    /// token in expression position and needs to rescan it as a regex.
    /// It does not restore on failure - it emits an error and returns a Regex
    /// token with empty pattern on unterminated regex.
    pub fn scan_regex(&mut self, opening_pos: Position, prefix_length: usize) -> ScanResult<'src> {
        let start_pos = self.position();
        // The normal token is `/` or `/.`; restart at its ASCII opening
        // delimiter (res_scanner.ml `scan_regex`).
        self.offset -= prefix_length;
        self.char_pos -= prefix_length;
        self.offset16 = (opening_pos.cnum - opening_pos.bol) as usize;
        self.ch = '/';
        self.ch_len = 1;
        self.next();
        let pattern_start = self.offset;

        // OCaml `scan_regex` (compiler/syntax/src/res_scanner.ml:562-624).
        let mut in_char_class = false;

        let (pattern, flags) = loop {
            match self.ch {
                '/' if !in_char_class => {
                    let pattern = Cow::Borrowed(self.substring(pattern_start, self.offset));
                    self.next();
                    let flags_start = self.offset;
                    while matches!(self.ch, 'd' | 'g' | 'i' | 'm' | 's' | 'u' | 'v' | 'y') {
                        self.next();
                    }
                    let flags = Cow::Borrowed(self.substring(flags_start, self.offset));
                    break (pattern, flags);
                }
                c if c == '\n' || c == '\r' || c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(
                        start_pos,
                        end_pos,
                        DiagnosticCategory::message("unterminated regex".to_string()),
                    );
                    break (
                        Cow::Borrowed(self.substring(pattern_start, self.offset)),
                        Cow::Borrowed(""),
                    );
                }
                '\\' => {
                    self.next();
                    self.next();
                }
                '[' if !in_char_class => {
                    in_char_class = true;
                    self.next();
                }
                ']' if in_char_class => {
                    in_char_class = false;
                    self.next();
                }
                _ => self.next(),
            }
        };

        let end_pos = self.position();
        ScanResult {
            start_pos: opening_pos,
            end_pos,
            token: Token::Regex { pattern, flags },
        }
    }

    /// Scan an escape sequence in a character literal.
    fn scan_escape(&mut self) -> Token<'src> {
        // offset points to the first char after '\, and we want to capture from
        // the char before that (the backslash escape char in the source).
        // In the old code: `let offset = self.offset - 1` (char index).
        // In byte mode: we need the byte offset of the previous character.
        // Since the caller did next2() (skipping ' then \), the char before current
        // is '\' which is ASCII (1 byte), so offset - 1 is correct.
        let escape_byte_start = self.offset - 1;

        let codepoint = match self.ch {
            '0'..='9' => self.convert_number(3, 10),
            'b' => {
                self.next();
                8
            }
            'n' => {
                self.next();
                10
            }
            'r' => {
                self.next();
                13
            }
            't' => {
                self.next();
                9
            }
            'x' => {
                self.next();
                self.convert_number(2, 16)
            }
            'o' => {
                self.next();
                self.convert_number(3, 8)
            }
            'u' => {
                self.next();
                if self.ch == '{' {
                    self.next();
                    let mut x = 0;
                    while self.ch.is_ascii_hexdigit() {
                        x = x * 16 + Self::digit_value(self.ch) as i32;
                        self.next();
                    }
                    if self.ch == '}' {
                        self.next();
                    }
                    if utf8::is_valid_codepoint(x) {
                        x
                    } else {
                        utf8::REPLACEMENT_CHAR
                    }
                } else {
                    self.convert_number(4, 16)
                }
            }
            ch => {
                self.next();
                ch as i32
            }
        };

        // Capture the escape sequence contents BEFORE consuming the closing quote
        let contents = Cow::Borrowed(self.substring(escape_byte_start, self.offset));

        // OCaml res_scanner.ml scan_escape: `next scanner` unconditionally
        // (the closing quote is assumed, not checked).
        self.next();

        Token::Codepoint {
            c: codepoint,
            original: contents,
        }
    }

    /// Convert a sequence of digits to a number.
    fn convert_number(&mut self, n: usize, base: u32) -> i32 {
        // res_scanner.ml:495-503: exactly `n` chars are consumed and
        // accumulated, digits or not.
        let mut x = 0i32;
        for _ in 0..n {
            let d = Self::digit_value(self.ch);
            x = x * base as i32 + d as i32;
            self.next();
        }
        if utf8::is_valid_codepoint(x) {
            x
        } else {
            utf8::REPLACEMENT_CHAR
        }
    }

    /// Scan an exotic identifier or its recovery form, matching OCaml's scanner.
    fn scan_exotic_identifier(&mut self, start_pos: Position) -> Token<'src> {
        let start_offset = self.offset;
        self.next2();

        loop {
            match self.ch {
                '"' => {
                    self.next();
                    break;
                }
                '\n' | '\r' => {
                    let end_pos = self.position();
                    self.error(
                        start_pos,
                        end_pos,
                        DiagnosticCategory::message(
                            "A quoted identifier can't contain line breaks.",
                        ),
                    );
                    self.next();
                    break;
                }
                c if c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(
                        start_pos,
                        end_pos,
                        DiagnosticCategory::message("Did you forget a \" here?"),
                    );
                    break;
                }
                _ => self.next(),
            }
        }

        let ident = self.substring(start_offset, self.offset);
        let name = Self::unwrap_uppercase_exotic(ident);
        if name.is_empty() {
            let end_pos = self.position();
            self.error(
                start_pos,
                end_pos,
                DiagnosticCategory::message("A quoted identifier can't be empty string."),
            );
            Token::Lident(Cow::Borrowed(ident))
        } else if name == "_" {
            // `_` is the wildcard and the placeholder of underscore apply
            // sugar; a quoted `_` couldn't be told apart from them.
            let end_pos = self.position();
            self.error(
                start_pos,
                end_pos,
                DiagnosticCategory::message("`_` can't be used as a quoted identifier."),
            );
            Token::Lident(Cow::Borrowed(name))
        } else if Self::is_uident(name) {
            Token::Lident(Cow::Borrowed(ident))
        } else {
            Token::Lident(Cow::Borrowed(name))
        }
    }

    fn is_uident(name: &str) -> bool {
        name.as_bytes()
            .first()
            .is_some_and(|byte| byte.is_ascii_uppercase())
    }

    fn unwrap_uppercase_exotic(name: &str) -> &str {
        if name.len() >= 3 && name.starts_with("\\\"") && name.ends_with('"') {
            &name[2..name.len() - 1]
        } else {
            name
        }
    }

    /// Check if an operator has whitespace on both sides (making it binary).
    ///
    /// `cnum` values are char indices (which equal original byte offsets in
    /// Latin-1 mode, as in OCaml `Scanner.isBinaryOp`), not offsets into the
    /// UTF-8 `src`, so the chars are located with `char_at_cnum`.
    pub fn is_binary_op(&self, start_cnum: usize, end_cnum: usize) -> bool {
        if start_cnum == 0 {
            return false;
        }
        let left_ok = self
            .char_at_cnum(start_cnum - 1)
            .is_some_and(Self::is_whitespace);
        // Past the end of the source counts as whitespace on the right.
        let right_ok = self.char_at_cnum(end_cnum).is_none_or(Self::is_whitespace);
        left_ok && right_ok
    }

    /// The char at char index `cnum`, or `None` past the end of the source.
    ///
    /// Walks from the scanner's current position (char `char_pos` at byte
    /// `offset`), which is next to the token the parser is looking at, so this
    /// costs the distance between the two rather than a scan from the start.
    fn char_at_cnum(&self, cnum: usize) -> Option<char> {
        let mut byte = self.offset.min(self.bytes.len());
        let mut pos = self.char_pos;
        if cnum >= pos {
            return self.src[byte..].chars().nth(cnum - pos);
        }
        while pos > cnum {
            byte -= 1;
            while byte > 0 && self.bytes[byte] & 0xC0 == 0x80 {
                byte -= 1;
            }
            pos -= 1;
        }
        self.src[byte..].chars().next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_arena::ParseArena;

    #[test]
    fn test_scan_identifier() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "hello world");
        let result = scanner.scan();
        assert_eq!(result.token, Token::Lident(Cow::Borrowed("hello")));

        let result = scanner.scan();
        assert_eq!(result.token, Token::Lident(Cow::Borrowed("world")));
    }

    /// tests/syntax_tests/res_test.ml:89-137: the scanner skips a UTF-8 byte
    /// order mark and ends a line at a CR without an LF, and code frames show
    /// the lines the positions refer to.
    #[test]
    fn byte_order_mark_and_lone_cr() {
        fn parse(
            source: &str,
        ) -> (
            crate::parser::Parser<'_>,
            Vec<crate::parser::ast::StructureItem>,
        ) {
            let mut parser = crate::parser::Parser::new("bom.res", source);
            let structure = crate::parser::module::parse_structure(&mut parser);
            assert!(!parser.has_errors(), "{source:?}");
            (parser, structure)
        }
        fn position_of_y(source: &str) -> crate::location::Position {
            let (parser, structure) = parse(source);
            *parser.arena().loc_start(structure[1].pstr_loc)
        }
        let line_and_column = |pos: crate::location::Position| (pos.line, pos.cnum - pos.bol);
        let bom = "\u{EF}\u{BB}\u{BF}";
        let source = format!("{bom}let x = 1");
        let (parser, structure) = parse(&source);
        assert_eq!(structure.len(), 1);
        assert_eq!(
            line_and_column(*parser.arena().loc_start(structure[0].pstr_loc)),
            (1, 0)
        );
        // Sources are read as Latin-1, one char per byte, so the first line
        // starts at byte 3, after the mark, as `line_offset = offset` does
        // in res_scanner.ml.
        let start = *parser.arena().loc_start(structure[0].pstr_loc);
        assert_eq!((start.bol, start.cnum), (3, 3));
        for (source, expected) in [
            ("let x = 1\rlet y = 2".to_string(), (2, 0)),
            ("let x = 1 // c\rlet y = 2".to_string(), (2, 0)),
            ("let x = 1 /* c */\r  let y = 2".to_string(), (2, 2)),
            ("let x = 1\r\nlet y = 2".to_string(), (2, 0)),
            ("let x = 1\r\rlet y = 2".to_string(), (3, 0)),
            ("let x = 1\n\rlet y = 2".to_string(), (3, 0)),
            (format!("{bom}let x = 1; let y = 2"), (1, 11)),
            (format!("{bom}let x = 1\rlet y = 2"), (2, 0)),
        ] {
            assert_eq!(
                line_and_column(position_of_y(&source)),
                expected,
                "{source:?}"
            );
        }
        // A regex literal ends at a line break.
        let mut parser = crate::parser::Parser::new("regex.res", "let r = /a\rb/");
        crate::parser::module::parse_structure(&mut parser);
        assert!(parser.has_errors());
        // Code frames show the lines the positions refer to.
        let frame = |source: &str| {
            let start = position_of_y(source);
            let end = crate::location::Position {
                cnum: start.cnum + 3,
                ..start
            };
            let printed = crate::parser::code_frame::print(source, &start, &end);
            let mut plain = String::new();
            let mut chars = printed.chars();
            while let Some(c) = chars.next() {
                if c == '\u{1b}' {
                    for c in chars.by_ref() {
                        if c == 'm' {
                            break;
                        }
                    }
                } else {
                    plain.push(c);
                }
            }
            plain
        };
        assert_eq!(
            frame(&format!("{bom}let x = 1; let y = 2")),
            "  1 │ let x = 1; let y = 2\n"
        );
        assert_eq!(
            frame("let x = 1\rlet y = 2\rlet z = 3"),
            "  1 │ let x = 1\n  2 │ let y = 2\n  3 │ let z = 3\n"
        );
    }

    #[test]
    fn unknown_characters_keep_first_start_and_report_each() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let src = format!("a {}b", "\u{1}".repeat(3));
        let mut scanner = Scanner::new(filename, &src);
        scanner.scan();
        let result = scanner.scan();
        assert_eq!(result.token, Token::Lident(Cow::Borrowed("b")));
        assert_eq!(result.start_pos.cnum, 2);
        assert_eq!(result.end_pos.cnum, 6);
        assert_eq!(scanner.take_diagnostics().len(), 3);
    }

    #[test]
    fn long_runs_of_unknown_characters_do_not_recurse() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let src = format!("{}b", "\u{1}".repeat(200_000));
        let mut scanner = Scanner::new(filename, &src);
        let result = scanner.scan();
        assert_eq!(result.token, Token::Lident(Cow::Borrowed("b")));
        assert_eq!(result.start_pos.cnum, 0);
    }

    #[test]
    fn string_literals_borrow_unless_escaped() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, r#""plain" "a\065\n""#);
        let plain = scanner.scan().token;
        assert!(matches!(plain, Token::String(Cow::Borrowed("plain"))));
        let escaped = scanner.scan().token;
        assert_eq!(escaped, Token::String(Cow::Owned("a\\x41\\n".to_string())));
    }

    #[test]
    fn is_binary_op_matches_whole_source_char_indexing() {
        fn reference(src: &str, start_cnum: usize, end_cnum: usize) -> bool {
            if start_cnum == 0 {
                return false;
            }
            let chars: Vec<char> = src.chars().collect();
            let left_ok =
                start_cnum <= chars.len() && Scanner::is_whitespace(chars[start_cnum - 1]);
            let right_ok = end_cnum >= chars.len() || Scanner::is_whitespace(chars[end_cnum]);
            left_ok && right_ok
        }
        for src in [
            "let x = a - b\n-1",
            "let s = \"\u{e9}\u{c3}\u{a9}\" - x < y\n<div/>",
            "\u{e9}\u{e9} -x %e -. y-z",
            "a -",
        ] {
            let mut arena = ParseArena::new();
            let filename = arena.intern("test.res");
            let mut scanner = Scanner::new(filename, src);
            loop {
                let result = scanner.scan();
                let start = result.start_pos.cnum as usize;
                let end = result.end_pos.cnum as usize;
                assert_eq!(
                    scanner.is_binary_op(start, end),
                    reference(src, start, end),
                    "{src:?} token at {start}..{end}"
                );
                for cnum in 0..start {
                    assert_eq!(scanner.char_at_cnum(cnum), src.chars().nth(cnum));
                }
                if result.token == Token::Eof {
                    break;
                }
            }
        }
    }

    #[test]
    fn test_scan_keyword() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "let if else");
        assert_eq!(scanner.scan().token, Token::Let { unwrap: false });
        assert_eq!(scanner.scan().token, Token::If);
        assert_eq!(scanner.scan().token, Token::Else);
    }

    #[test]
    fn test_scan_number() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "42 3.14 0xFF");

        let result = scanner.scan();
        assert!(matches!(result.token, Token::Int { i, .. } if i == "42"));

        let result = scanner.scan();
        assert!(matches!(result.token, Token::Float { f, .. } if f == "3.14"));

        let result = scanner.scan();
        assert!(matches!(result.token, Token::Int { i, .. } if i == "0xFF"));
    }

    #[test]
    fn test_scan_string() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "\"hello\"");
        let result = scanner.scan();
        assert!(matches!(result.token, Token::String(s) if s == "hello"));
    }

    #[test]
    fn test_scan_operators() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "+ - * / == => ->");

        assert_eq!(scanner.scan().token, Token::Plus);
        assert_eq!(scanner.scan().token, Token::Minus);
        assert_eq!(scanner.scan().token, Token::Asterisk);
        assert_eq!(scanner.scan().token, Token::Forwardslash);
        assert_eq!(scanner.scan().token, Token::EqualEqual);
        assert_eq!(scanner.scan().token, Token::EqualGreater);
        assert_eq!(scanner.scan().token, Token::MinusGreater);
    }

    #[test]
    fn test_scan_comment() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "// comment\nfoo");

        let result = scanner.scan();
        assert!(matches!(result.token, Token::Comment(_)));

        let result = scanner.scan();
        assert_eq!(result.token, Token::Lident(Cow::Borrowed("foo")));
    }

    #[test]
    fn test_scan_multiline_comment() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "/* comment */ foo");

        let result = scanner.scan();
        assert!(matches!(result.token, Token::Comment(_)));

        let result = scanner.scan();
        assert_eq!(result.token, Token::Lident(Cow::Borrowed("foo")));
    }

    #[test]
    fn test_scan_eof() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "");
        assert_eq!(scanner.scan().token, Token::Eof);
    }

    #[test]
    fn test_position_tracking() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "let\nfoo");

        let result = scanner.scan();
        assert_eq!(result.start_pos.line, 1);

        let result = scanner.scan();
        assert_eq!(result.start_pos.line, 2);
    }

    #[test]
    fn test_binary_operator_suffix() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, ">> > =");

        // `>` is always scanned alone; the parser extends adjacent suffixes.
        let result = scanner.scan();
        assert_eq!(result.token, Token::GreaterThan);
        assert_eq!(
            scanner.scan_binary_operator(&result.token),
            Some(Token::RightShift)
        );
        let result = scanner.scan();
        assert_eq!(result.token, Token::GreaterThan);
        // Trivia is never skipped.
        assert_eq!(scanner.scan_binary_operator(&result.token), None);
    }

    #[test]
    fn test_list_dict_let_special() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, "list{ dict{ let?");

        assert_eq!(scanner.scan().token, Token::List);
        assert_eq!(scanner.scan().token, Token::Dict);
        assert_eq!(scanner.scan().token, Token::Let { unwrap: true });
    }
}
