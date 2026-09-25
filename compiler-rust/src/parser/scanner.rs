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
//! - No upfront Vec<char> or Vec<usize> allocation

use std::borrow::Cow;

use crate::intern::StrIdx;
use crate::location::Position;

use super::comment::{Comment, CommentStyle};
use super::diagnostics::{DiagnosticCategory, ParserDiagnostic};
use super::token::Token;
use super::utf8;

/// Special character value indicating end of file.
/// We use a value outside the valid char range.
const EOF_CHAR: char = '\u{FFFF}';

/// Scanner mode for context-sensitive tokenization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScannerMode {
    /// Diamond mode for type parameter parsing (affects `>` tokenization).
    Diamond,
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
    mode: Vec<ScannerMode>,
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
    /// Stack of scanner modes.
    mode: Vec<ScannerMode>,
    /// Collected diagnostics.
    diagnostics: Vec<ParserDiagnostic>,
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
        let (ch, ch_len) = if bytes.is_empty() {
            (EOF_CHAR, 0)
        } else if bytes[0] < 0x80 {
            (bytes[0] as char, 1)
        } else {
            let (cp, len) = utf8::decode_codepoint(bytes, 0);
            (char::from_u32(cp as u32).unwrap_or(EOF_CHAR), len)
        };

        Self {
            filename,
            src,
            bytes,
            ch,
            ch_len,
            offset: 0,
            char_pos: 0,
            offset16: 0,
            line_offset: 0,
            lnum: 1,
            mode: Vec::new(),
            diagnostics: Vec::new(),
        }
    }

    /// Get collected diagnostics.
    pub fn diagnostics(&self) -> &[ParserDiagnostic] {
        &self.diagnostics
    }

    /// Take collected diagnostics, leaving an empty vec.
    pub fn take_diagnostics(&mut self) -> Vec<ParserDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Push diamond mode for type parameter parsing.
    pub fn set_diamond_mode(&mut self) {
        self.mode.push(ScannerMode::Diamond);
    }

    /// Pop diamond mode.
    pub fn pop_diamond_mode(&mut self) {
        if let Some(ScannerMode::Diamond) = self.mode.last() {
            self.mode.pop();
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
            mode: self.mode.clone(),
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
        self.mode = snapshot.mode;
        self.diagnostics.truncate(snapshot.diagnostics_len);
    }

    /// Get a reference to the source string.
    pub fn src(&self) -> &str {
        self.src
    }

    /// Check if in diamond mode.
    pub fn in_diamond_mode(&self) -> bool {
        matches!(self.mode.last(), Some(ScannerMode::Diamond))
    }

    /// Get the current position.
    ///
    /// For OCaml parity, we use `line_offset + offset16` for cnum.
    /// This matches OCaml where `pos_cnum = scanner.line_offset + scanner.offset16`,
    /// giving us UTF-16 code unit counting for columns.
    /// `line_offset` and `char_pos` are character-indexed (not byte-indexed)
    /// to preserve binary AST parity with the OCaml implementation.
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
    /// column counting. The UTF-16 length is computed by interpreting the character's
    /// codepoint as a raw byte pattern (matching OCaml's behavior for Latin-1 source):
    /// - ASCII (0x00-0x7F): 1
    /// - "Continuation" pattern (0x80-0xBF): 0
    /// - "2-byte leading" pattern (0xC0-0xDF): 1
    /// - "3-byte leading" pattern (0xE0-0xEF): 1
    /// - "4-byte leading" pattern (0xF0-0xF7): 2
    fn next(&mut self) {
        if self.offset >= self.bytes.len() {
            self.ch = EOF_CHAR;
            self.ch_len = 0;
            return;
        }

        let next_char_pos = self.char_pos + 1;

        // Calculate UTF-16 length using the character's codepoint value interpreted
        // as a raw byte pattern. This matches the old code which did `self.ch as u32`
        // and classified it using UTF-8 byte-pattern rules. This is critical for parity
        // because the source is Latin-1 encoded (each original byte → one char), and
        // OCaml's scanner uses byte-level classification for position tracking.
        //
        // For Latin-1 chars 0x80-0xBF: treated as "continuation bytes" → utf16len = 0
        // For Latin-1 chars 0xC0-0xDF: treated as "2-byte leading" → utf16len = 1
        // For Latin-1 chars 0xE0-0xEF: treated as "3-byte leading" → utf16len = 1
        // For Latin-1 chars 0xF0-0xF7: treated as "4-byte leading" → utf16len = 2
        let byte = self.ch as u32;
        let utf16len = if byte & 0x80 == 0 {
            // ASCII: 1 UTF-16 code unit
            1
        } else if byte & 0x40 == 0 {
            // Continuation byte pattern (Latin-1 0x80-0xBF): 0
            0
        } else if byte & 0x20 == 0 {
            // 2-byte leading pattern (Latin-1 0xC0-0xDF): 1
            1
        } else if byte & 0x10 == 0 {
            // 3-byte leading pattern (Latin-1 0xE0-0xEF): 1
            1
        } else if byte & 0x08 == 0 {
            // 4-byte leading pattern (Latin-1 0xF0-0xF7): 2
            2
        } else {
            // Invalid byte pattern
            1
        };

        // Handle newlines - update line tracking
        if self.ch == '\n' {
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

    /// Peek at the next character without advancing.
    ///
    /// Uses byte-level access: skips past current character's bytes to find the next.
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

    fn peek(&self) -> char {
        let next_offset = self.offset + self.ch_len;
        if next_offset >= self.bytes.len() {
            return EOF_CHAR;
        }
        let b = self.bytes[next_offset];
        if b < 0x80 {
            b as char
        } else {
            let (cp, _) = utf8::decode_codepoint(self.bytes, next_offset);
            char::from_u32(cp as u32).unwrap_or(EOF_CHAR)
        }
    }

    /// Peek at the character 2 positions ahead.
    fn peek2(&self) -> char {
        let mut off = self.offset + self.ch_len;
        if off >= self.bytes.len() {
            return EOF_CHAR;
        }
        // Skip one character
        let b1 = self.bytes[off];
        if b1 < 0x80 {
            off += 1;
        } else {
            let (_, len) = utf8::decode_codepoint(self.bytes, off);
            off += len;
        }
        // Decode the second character ahead
        if off >= self.bytes.len() {
            return EOF_CHAR;
        }
        let b2 = self.bytes[off];
        if b2 < 0x80 {
            b2 as char
        } else {
            let (cp, _) = utf8::decode_codepoint(self.bytes, off);
            char::from_u32(cp as u32).unwrap_or(EOF_CHAR)
        }
    }

    /// Peek at the character 3 positions ahead.
    fn peek3(&self) -> char {
        let mut off = self.offset + self.ch_len;
        // Skip two characters
        for _ in 0..2 {
            if off >= self.bytes.len() {
                return EOF_CHAR;
            }
            let b = self.bytes[off];
            if b < 0x80 {
                off += 1;
            } else {
                let (_, len) = utf8::decode_codepoint(self.bytes, off);
                off += len;
            }
        }
        // Decode the third character ahead
        if off >= self.bytes.len() {
            return EOF_CHAR;
        }
        let b = self.bytes[off];
        if b < 0x80 {
            b as char
        } else {
            let (cp, _) = utf8::decode_codepoint(self.bytes, off);
            char::from_u32(cp as u32).unwrap_or(EOF_CHAR)
        }
    }

    /// Check if a character is whitespace.
    fn is_whitespace(ch: char) -> bool {
        matches!(ch, ' ' | '\t' | '\n' | '\r')
    }

    /// Skip whitespace characters.
    fn skip_whitespace(&mut self) {
        while Self::is_whitespace(self.ch) {
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
        while matches!(self.ch, 'A'..='Z' | 'a'..='z' | '0'..='9' | '_' | '\'') {
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
        // We use a buffer to accumulate the result, copying text verbatim except
        // for decimal escapes which get converted to hex format.
        let mut result = String::new();
        let mut chunk_start = self.offset;

        loop {
            match self.ch {
                '"' => {
                    // Add remaining content
                    result.push_str(self.substring(chunk_start, self.offset));
                    self.next();
                    break;
                }
                '\\' => {
                    // Add content before the escape (including the backslash)
                    result.push_str(self.substring(chunk_start, self.offset));
                    result.push('\\');
                    let escape_start_pos = self.position();
                    self.next(); // consume backslash

                    // Check if this is a decimal escape that needs conversion
                    let escape_start = self.offset;
                    self.scan_string_escape_sequence_text(&escape_start_pos);
                    let escape_end = self.offset;

                    // Check if it was a 3-digit decimal escape
                    let escape_text = self.substring(escape_start, escape_end);
                    if escape_text.len() == 3 && escape_text.chars().all(|c| c.is_ascii_digit()) {
                        // Convert decimal to hex format
                        if let Ok(value) = escape_text.parse::<u32>() {
                            if value <= 255 {
                                result.push_str(&format!("x{:02x}", value));
                            } else {
                                // Invalid value, keep as-is
                                result.push_str(escape_text);
                            }
                        } else {
                            result.push_str(escape_text);
                        }
                    } else {
                        // Keep other escapes as-is
                        result.push_str(escape_text);
                    }
                    chunk_start = self.offset;
                }
                c if c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(start_pos, end_pos, DiagnosticCategory::unclosed_string());
                    result.push_str(self.substring(chunk_start, self.offset));
                    break;
                }
                _ => self.next(),
            }
        }

        Token::String(Cow::Owned(result))
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
                self.scan_string_escape_digits(start_pos, 3, 10, 255);
            }
            'x' => {
                // Hex escape \xNN
                self.next();
                self.scan_string_escape_digits(start_pos, 2, 16, 255);
            }
            'u' => {
                self.next();
                if self.ch == '{' {
                    // Unicode escape \u{NNNN}
                    self.next();
                    while self.ch.is_ascii_hexdigit() {
                        self.next();
                    }
                    if self.ch == '}' {
                        self.next();
                    }
                } else {
                    // Unicode escape \uNNNN, exactly four hex digits.
                    self.scan_string_escape_digits(start_pos, 4, 16, 0x10FFFF);
                }
            }
            _ => {
                // OCaml `scan_string_escape_sequence` (res_scanner.ml:405-416):
                // an unknown escape, or the end of input, is left to the
                // string loop without a diagnostic.
            }
        }
    }

    fn scan_string_escape_digits(
        &mut self,
        start_pos: &Position,
        digits: usize,
        base: u32,
        max: u32,
    ) {
        let mut value = 0;

        for _ in 0..digits {
            let Some(digit) = self.ch.to_digit(base) else {
                let end_pos = self.position();
                let message = if self.ch == EOF_CHAR {
                    "unclosed escape sequence"
                } else {
                    "unknown escape sequence"
                };
                self.error(
                    start_pos.clone(),
                    end_pos,
                    DiagnosticCategory::message(message),
                );
                return;
            };
            self.next();
            value = (value * base) + digit;
        }

        if value > max || (0xD800..0xE000).contains(&value) {
            let end_pos = self.position();
            self.error(
                start_pos.clone(),
                end_pos,
                DiagnosticCategory::message("escape sequence is invalid unicode code point"),
            );
        }
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
        let content_start_off = {
            let mut off = self.offset;
            for _ in 0..content_char_skip {
                if off >= self.bytes.len() {
                    break;
                }
                let b = self.bytes[off];
                if b < 0x80 {
                    off += 1;
                } else {
                    let (_, len) = utf8::decode_codepoint(self.bytes, off);
                    off += len;
                }
            }
            off
        };

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
                    self.error(
                        start_pos.clone(),
                        end_pos,
                        DiagnosticCategory::unclosed_comment(),
                    );
                    break;
                }
                _ => self.next(),
            }
        }

        // Content ends 2 bytes before current position (before closing */)
        // But we need to compute this in byte offsets
        let content_end_off = if self.offset >= 2 {
            // Walk back 2 characters from current byte offset
            // Since */ is ASCII, we just subtract 2 bytes
            self.offset - 2
        } else {
            0
        };

        let content: Cow<'src, str> =
            if content_start_off <= content_end_off && content_start_off < self.src.len() {
                Cow::Borrowed(self.substring(content_start_off, content_end_off))
            } else {
                Cow::Borrowed("")
            };

        let end_pos = self.position();
        let loc = crate::location::Location::from_positions(start_pos, end_pos);

        if doc_comment {
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
            })
        }
    }

    /// Scan a template literal token.
    pub fn scan_template_literal_token(&mut self) -> ScanResult<'src> {
        let start_off = self.offset;

        // If starting with }, consume it
        if self.ch == '}' {
            self.next();
        }

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
                    self.error(
                        start_pos.clone(),
                        end_pos.clone(),
                        DiagnosticCategory::unclosed_template(),
                    );
                    // OCaml uses (max (scanner.offset - 1 - start_off) 0) to exclude the last char
                    let end_off = if self.offset > start_off {
                        // Go back 1 character's worth of bytes
                        // At EOF, the previous char was the last real char
                        // We need to compute its byte offset
                        self.offset.saturating_sub(1).max(start_off)
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
        self.skip_whitespace();
        let start_pos = self.position();

        let token = match self.ch {
            // Identifiers and keywords
            'A'..='Z' | 'a'..='z' => self.scan_identifier(),

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
                if matches!(self.peek(), 'A'..='Z' | 'a'..='z' | '0'..='9' | '_') {
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

            '>' if !self.in_diamond_mode() => match self.peek() {
                '=' => {
                    self.next2();
                    Token::GreaterEqual
                }
                '>' => {
                    if self.peek2() == '>' {
                        self.next3();
                        Token::RightShiftUnsigned
                    } else {
                        self.next2();
                        Token::RightShift
                    }
                }
                _ => {
                    self.next();
                    Token::GreaterThan
                }
            },
            '>' => {
                self.next();
                Token::GreaterThan
            }

            '<' => match self.peek() {
                '<' if !self.in_diamond_mode() => {
                    self.next2();
                    Token::LeftShift
                }
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
                    let original =
                        Cow::Borrowed(self.substring(char_byte_off, char_byte_off + ch.len_utf8()));
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
                    let (codepoint, length) = self.decode_codepoint_from_latin1_source(self.offset);

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
                self.error(
                    start_pos.clone(),
                    end_pos,
                    DiagnosticCategory::unknown_uchar(ch),
                );
                // Continue scanning - but preserve the original start_pos
                // OCaml: let _, _, token = scan scanner in token
                // (start_pos, end_pos, token) - uses outer start_pos, not recursive one
                let scan_result = self.scan();
                return ScanResult {
                    start_pos, // Use the outer start_pos (before the bad character)
                    end_pos: scan_result.end_pos,
                    token: scan_result.token,
                };
            }
        };

        let end_pos = self.position();
        ScanResult {
            start_pos,
            end_pos,
            token,
        }
    }

    /// Scan a regex literal from the current position (after the opening `/` has been consumed).
    /// This matches OCaml's `scan_regex` which is called by the parser when it encounters a `/`
    /// token in expression position and needs to rescan it as a regex.
    /// Unlike `try_scan_regex_literal`, this does not restore on failure - it emits an error
    /// and returns a Regex token with empty pattern on unterminated regex.
    pub fn scan_regex(&mut self) -> ScanResult<'src> {
        let start_pos = self.position();
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
                c if c == '\n' || c == EOF_CHAR => {
                    let end_pos = self.position();
                    self.error(
                        start_pos.clone(),
                        end_pos,
                        DiagnosticCategory::message("unterminated regex".to_string()),
                    );
                    break (Cow::Borrowed(""), Cow::Borrowed(""));
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
            start_pos,
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

        // Consume closing quote
        if self.ch == '\'' {
            self.next();
        }

        Token::Codepoint {
            c: codepoint,
            original: contents,
        }
    }

    /// Convert a sequence of digits to a number.
    fn convert_number(&mut self, n: usize, base: u32) -> i32 {
        let mut x = 0i32;
        for _ in 0..n {
            let d = Self::digit_value(self.ch);
            if d < base {
                x = x * base as i32 + d as i32;
                self.next();
            }
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
                        start_pos.clone(),
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
                        start_pos.clone(),
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
    /// Uses char-based indexing since `cnum` values are char indices (which equal
    /// original byte offsets in Latin-1 mode). We cannot use `src.as_bytes()` because
    /// the Rust string's UTF-8 representation has different byte offsets for non-ASCII
    /// Latin-1 chars (each Latin-1 char 128-255 becomes 2 UTF-8 bytes).
    pub fn is_binary_op(src: &str, start_cnum: usize, end_cnum: usize) -> bool {
        if start_cnum == 0 {
            return false;
        }

        let src_chars: Vec<char> = src.chars().collect();
        let left_ok = start_cnum > 0
            && start_cnum <= src_chars.len()
            && Self::is_whitespace(src_chars[start_cnum - 1]);

        let right_ok = end_cnum >= src_chars.len() || Self::is_whitespace(src_chars[end_cnum]);

        left_ok && right_ok
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
    fn test_diamond_mode() {
        let mut arena = ParseArena::new();
        let filename = arena.intern("test.res");
        let mut scanner = Scanner::new(filename, ">> >");

        // Normal mode: >> is right shift
        let result = scanner.scan();
        assert_eq!(result.token, Token::RightShift);

        // In diamond mode: > is just greater than
        scanner.set_diamond_mode();
        let result = scanner.scan();
        assert_eq!(result.token, Token::GreaterThan);
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
