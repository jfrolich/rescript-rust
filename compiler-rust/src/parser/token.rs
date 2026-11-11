//! Token definitions for the ReScript parser.
//!
//! This module defines all tokens that can appear in ReScript source code,
//! along with utilities for token classification, precedence, and conversion.
//!
//! Tokens use `Cow<'a, str>` for string data, enabling zero-copy borrowing
//! from source for identifiers and literals that don't need transformation,
//! while still supporting owned strings for escape-processed content.

use std::borrow::Cow;

use super::comment::Comment;
use crate::location::{Location, Position};
use serde::{Deserialize, Serialize};

/// A token in ReScript source code.
///
/// The lifetime `'a` refers to the source string being scanned.
/// Most string data (identifiers, numbers) borrows from source via `Cow::Borrowed`.
/// Strings that need transformation (escape sequences) use `Cow::Owned`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Token<'a> {
    // Keywords
    /// `await` keyword
    Await,
    /// `open` keyword
    Open,
    /// `break` keyword (upstream #8348)
    Break,
    /// `continue` keyword (upstream #8348)
    Continue,
    /// `true` literal
    True,
    /// `false` literal
    False,
    /// `as` keyword
    As,
    /// `and` keyword
    And,
    /// `rec` keyword
    Rec,
    /// `exception` keyword
    Exception,
    /// `assert` keyword
    Assert,
    /// `if` keyword
    If,
    /// `else` keyword
    Else,
    /// `for` keyword
    For,
    /// `in` keyword
    In,
    /// `while` keyword
    While,
    /// `switch` keyword
    Switch,
    /// `when` keyword
    When,
    /// `external` keyword
    External,
    /// `type` keyword
    Typ,
    /// `private` keyword
    Private,
    /// `mutable` keyword
    Mutable,
    /// `constraint` keyword
    Constraint,
    /// `include` keyword
    Include,
    /// `module` keyword
    Module,
    /// `of` keyword
    Of,
    /// `try` keyword
    Try,
    /// `list{` keyword
    List,
    /// `dict{` keyword
    Dict,

    // Literals with data
    /// Unicode codepoint: `'\u{...}'`
    Codepoint {
        /// The codepoint value.
        c: i32,
        /// The original string representation.
        original: Cow<'a, str>,
    },
    /// Integer literal: `123`, `0xff`, etc.
    Int {
        /// The integer value as a string.
        i: Cow<'a, str>,
        /// Optional suffix like `n` for bigint.
        suffix: Option<char>,
    },
    /// Float literal: `1.0`, `1e10`, etc.
    Float {
        /// The float value as a string.
        f: Cow<'a, str>,
        /// Optional suffix.
        suffix: Option<char>,
    },
    /// String literal: `"hello"`
    String(Cow<'a, str>),
    /// Lowercase identifier: `foo`, `bar`
    Lident(Cow<'a, str>),
    /// Uppercase identifier: `Foo`, `Bar`
    Uident(Cow<'a, str>),
    /// Regular expression literal: `/pattern/flags`
    Regex {
        /// The regex pattern.
        pattern: Cow<'a, str>,
        /// The regex flags.
        flags: Cow<'a, str>,
    },

    // Let with optional unwrap
    /// `let` keyword, optionally with `?` for unwrap
    Let {
        /// Whether this is `let?` (unwrap binding)
        unwrap: bool,
    },

    // Punctuation
    /// `.`
    Dot,
    /// `..`
    DotDot,
    /// `...`
    DotDotDot,
    /// `!`
    Bang,
    /// `;`
    Semicolon,
    /// `_`
    Underscore,
    /// `'`
    SingleQuote,
    /// `=`
    Equal,
    /// `==`
    EqualEqual,
    /// `===`
    EqualEqualEqual,
    /// `&`
    Ampersand,
    /// `|`
    Bar,
    /// `(`
    Lparen,
    /// `)`
    Rparen,
    /// `[`
    Lbracket,
    /// `]`
    Rbracket,
    /// `{`
    Lbrace,
    /// `}`
    Rbrace,
    /// `:`
    Colon,
    /// `,`
    Comma,
    /// End of file
    Eof,
    /// `/`
    Forwardslash,
    /// `/.`
    ForwardslashDot,
    /// `*`
    Asterisk,
    /// `*.`
    AsteriskDot,
    /// `**`
    Exponentiation,
    /// `-`
    Minus,
    /// `-.`
    MinusDot,
    /// `+`
    Plus,
    /// `+.`
    PlusDot,
    /// `++`
    PlusPlus,
    /// `+=`
    PlusEqual,
    /// `:>`
    ColonGreaterThan,
    /// `>`
    GreaterThan,
    /// `<`
    LessThan,
    /// `#`
    Hash,
    /// `#=`
    HashEqual,
    /// `~`
    Tilde,
    /// `?`
    Question,
    /// `=>`
    EqualGreater,
    /// `->`
    MinusGreater,
    /// `||` (logical or)
    Lor,
    /// `&&` (logical and)
    Land,
    /// `~~~` (bitwise not)
    Bnot,
    /// `|||` (bitwise or)
    Bor,
    /// `^^^` (bitwise xor)
    Bxor,
    /// `&&&` (bitwise and)
    Band,
    /// `^`
    Caret,
    /// `!=`
    BangEqual,
    /// `!==`
    BangEqualEqual,
    /// `<=`
    LessEqual,
    /// `>=`
    GreaterEqual,
    /// `:=`
    ColonEqual,
    /// `@`
    At,
    /// `@@`
    AtAt,
    /// `%`
    Percent,
    /// `%%`
    PercentPercent,
    /// `${`: opens a hole in a macro quote (`%code(...)`).
    DollarLbrace,
    /// ` `` ` (backtick)
    Backtick,
    /// `<<` (left shift)
    LeftShift,
    /// `>>` (right shift)
    RightShift,
    /// `>>>` (unsigned right shift)
    RightShiftUnsigned,

    // Comments
    /// A comment (single-line, multi-line, or doc comment)
    Comment(Comment),
    /// Doc comment with location and content
    DocComment {
        /// Location of the comment.
        loc: Location,
        /// Content of the comment.
        content: Cow<'a, str>,
    },
    /// Module comment with location and content
    ModuleComment {
        /// Location of the comment.
        loc: Location,
        /// Content of the comment.
        content: Cow<'a, str>,
    },

    // Template strings
    /// Template string tail: `...}`
    TemplateTail {
        /// The text content.
        text: Cow<'a, str>,
        /// The position of the tail.
        pos: Position,
    },
    /// Template string part: `...${`
    TemplatePart {
        /// The text content.
        text: Cow<'a, str>,
        /// The position of the part.
        pos: Position,
    },
}

impl<'a> Token<'a> {
    /// Get the precedence of a token for operator parsing.
    ///
    /// Returns 0 for non-operators.
    pub fn precedence(&self) -> i32 {
        match self {
            Token::HashEqual | Token::ColonEqual => 1,
            Token::Lor => 2,
            Token::Land => 3,
            Token::Bor => 4,
            Token::Bxor => 5,
            Token::Band => 6,
            Token::Equal
            | Token::EqualEqual
            | Token::EqualEqualEqual
            | Token::LessThan
            | Token::GreaterThan
            | Token::BangEqual
            | Token::BangEqualEqual
            | Token::LessEqual
            | Token::GreaterEqual => 7,
            Token::LeftShift | Token::RightShift | Token::RightShiftUnsigned => 8,
            Token::Plus | Token::PlusDot | Token::Minus | Token::MinusDot | Token::PlusPlus => 9,
            Token::Asterisk
            | Token::AsteriskDot
            | Token::Forwardslash
            | Token::ForwardslashDot
            | Token::Percent => 10,
            Token::Exponentiation => 11,
            Token::MinusGreater => 12,
            Token::Dot => 13,
            _ => 0,
        }
    }

    /// Check if this token is a keyword.
    pub fn is_keyword(&self) -> bool {
        matches!(
            self,
            Token::Await
                | Token::Break
                | Token::Continue
                | Token::And
                | Token::As
                | Token::Assert
                | Token::Constraint
                | Token::Else
                | Token::Exception
                | Token::External
                | Token::False
                | Token::For
                | Token::If
                | Token::In
                | Token::Include
                | Token::Land
                | Token::Let { .. }
                | Token::List
                | Token::Lor
                | Token::Module
                | Token::Mutable
                | Token::Of
                | Token::Open
                | Token::Private
                | Token::Rec
                | Token::Switch
                | Token::True
                | Token::Try
                | Token::Typ
                | Token::When
                | Token::While
                | Token::Dict
        )
    }

    /// Look up a keyword from a string, returning the appropriate token.
    ///
    /// If the string is not a keyword, returns an identifier token
    /// (Uident for uppercase, Lident for lowercase) borrowing from the source.
    pub fn lookup_keyword(s: &'a str) -> Token<'a> {
        match s {
            "and" => Token::And,
            "as" => Token::As,
            "assert" => Token::Assert,
            "await" => Token::Await,
            "break" => Token::Break,
            "constraint" => Token::Constraint,
            "continue" => Token::Continue,
            "else" => Token::Else,
            "exception" => Token::Exception,
            "external" => Token::External,
            "false" => Token::False,
            "for" => Token::For,
            "if" => Token::If,
            "in" => Token::In,
            "include" => Token::Include,
            "let?" => Token::Let { unwrap: true },
            "let" => Token::Let { unwrap: false },
            "list{" => Token::List,
            "dict{" => Token::Dict,
            "module" => Token::Module,
            "mutable" => Token::Mutable,
            "of" => Token::Of,
            "open" => Token::Open,
            "private" => Token::Private,
            "rec" => Token::Rec,
            "switch" => Token::Switch,
            "true" => Token::True,
            "try" => Token::Try,
            "type" => Token::Typ,
            "when" => Token::When,
            "while" => Token::While,
            _ => {
                // Check first byte to determine if Uident or Lident (ASCII check)
                if s.as_bytes().first().is_some_and(|b| b.is_ascii_uppercase()) {
                    Token::Uident(Cow::Borrowed(s))
                } else {
                    Token::Lident(Cow::Borrowed(s))
                }
            }
        }
    }

    /// Check if a string is a keyword.
    pub fn is_keyword_txt(s: &str) -> bool {
        !matches!(
            Token::lookup_keyword(s),
            Token::Lident(_) | Token::Uident(_)
        )
    }

    /// Convert this token into an owned version with `'static` lifetime.
    /// Used when storing tokens in diagnostics or other long-lived structures.
    pub fn into_owned(self) -> Token<'static> {
        match self {
            Token::Await => Token::Await,
            Token::Open => Token::Open,
            Token::Break => Token::Break,
            Token::Continue => Token::Continue,
            Token::True => Token::True,
            Token::False => Token::False,
            Token::As => Token::As,
            Token::And => Token::And,
            Token::Rec => Token::Rec,
            Token::Exception => Token::Exception,
            Token::Assert => Token::Assert,
            Token::If => Token::If,
            Token::Else => Token::Else,
            Token::For => Token::For,
            Token::In => Token::In,
            Token::While => Token::While,
            Token::Switch => Token::Switch,
            Token::When => Token::When,
            Token::External => Token::External,
            Token::Typ => Token::Typ,
            Token::Private => Token::Private,
            Token::Mutable => Token::Mutable,
            Token::Constraint => Token::Constraint,
            Token::Include => Token::Include,
            Token::Module => Token::Module,
            Token::Of => Token::Of,
            Token::Try => Token::Try,
            Token::List => Token::List,
            Token::Dict => Token::Dict,
            Token::Codepoint { c, original } => Token::Codepoint {
                c,
                original: Cow::Owned(original.into_owned()),
            },
            Token::Int { i, suffix } => Token::Int {
                i: Cow::Owned(i.into_owned()),
                suffix,
            },
            Token::Float { f, suffix } => Token::Float {
                f: Cow::Owned(f.into_owned()),
                suffix,
            },
            Token::String(s) => Token::String(Cow::Owned(s.into_owned())),
            Token::Lident(s) => Token::Lident(Cow::Owned(s.into_owned())),
            Token::Uident(s) => Token::Uident(Cow::Owned(s.into_owned())),
            Token::Regex { pattern, flags } => Token::Regex {
                pattern: Cow::Owned(pattern.into_owned()),
                flags: Cow::Owned(flags.into_owned()),
            },
            Token::Let { unwrap } => Token::Let { unwrap },
            Token::Dot => Token::Dot,
            Token::DotDot => Token::DotDot,
            Token::DotDotDot => Token::DotDotDot,
            Token::Bang => Token::Bang,
            Token::Semicolon => Token::Semicolon,
            Token::Underscore => Token::Underscore,
            Token::SingleQuote => Token::SingleQuote,
            Token::Equal => Token::Equal,
            Token::EqualEqual => Token::EqualEqual,
            Token::EqualEqualEqual => Token::EqualEqualEqual,
            Token::Ampersand => Token::Ampersand,
            Token::Bar => Token::Bar,
            Token::Lparen => Token::Lparen,
            Token::Rparen => Token::Rparen,
            Token::Lbracket => Token::Lbracket,
            Token::Rbracket => Token::Rbracket,
            Token::Lbrace => Token::Lbrace,
            Token::Rbrace => Token::Rbrace,
            Token::Colon => Token::Colon,
            Token::Comma => Token::Comma,
            Token::Eof => Token::Eof,
            Token::Forwardslash => Token::Forwardslash,
            Token::ForwardslashDot => Token::ForwardslashDot,
            Token::Asterisk => Token::Asterisk,
            Token::AsteriskDot => Token::AsteriskDot,
            Token::Exponentiation => Token::Exponentiation,
            Token::Minus => Token::Minus,
            Token::MinusDot => Token::MinusDot,
            Token::Plus => Token::Plus,
            Token::PlusDot => Token::PlusDot,
            Token::PlusPlus => Token::PlusPlus,
            Token::PlusEqual => Token::PlusEqual,
            Token::ColonGreaterThan => Token::ColonGreaterThan,
            Token::GreaterThan => Token::GreaterThan,
            Token::LessThan => Token::LessThan,
            Token::Hash => Token::Hash,
            Token::HashEqual => Token::HashEqual,
            Token::Tilde => Token::Tilde,
            Token::Question => Token::Question,
            Token::EqualGreater => Token::EqualGreater,
            Token::MinusGreater => Token::MinusGreater,
            Token::Lor => Token::Lor,
            Token::Land => Token::Land,
            Token::Bnot => Token::Bnot,
            Token::Bor => Token::Bor,
            Token::Bxor => Token::Bxor,
            Token::Band => Token::Band,
            Token::Caret => Token::Caret,
            Token::BangEqual => Token::BangEqual,
            Token::BangEqualEqual => Token::BangEqualEqual,
            Token::LessEqual => Token::LessEqual,
            Token::GreaterEqual => Token::GreaterEqual,
            Token::ColonEqual => Token::ColonEqual,
            Token::At => Token::At,
            Token::AtAt => Token::AtAt,
            Token::Percent => Token::Percent,
            Token::PercentPercent => Token::PercentPercent,
            Token::DollarLbrace => Token::DollarLbrace,
            Token::Backtick => Token::Backtick,
            Token::LeftShift => Token::LeftShift,
            Token::RightShift => Token::RightShift,
            Token::RightShiftUnsigned => Token::RightShiftUnsigned,
            Token::Comment(c) => Token::Comment(c),
            Token::DocComment { loc, content } => Token::DocComment {
                loc,
                content: Cow::Owned(content.into_owned()),
            },
            Token::ModuleComment { loc, content } => Token::ModuleComment {
                loc,
                content: Cow::Owned(content.into_owned()),
            },
            Token::TemplateTail { text, pos } => Token::TemplateTail {
                text: Cow::Owned(text.into_owned()),
                pos,
            },
            Token::TemplatePart { text, pos } => Token::TemplatePart {
                text: Cow::Owned(text.into_owned()),
                pos,
            },
        }
    }
}

impl<'a> std::fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Await => write!(f, "await"),
            Token::Break => write!(f, "break"),
            Token::Continue => write!(f, "continue"),
            Token::Open => write!(f, "open"),
            Token::True => write!(f, "true"),
            Token::False => write!(f, "false"),
            Token::Codepoint { original, .. } => write!(f, "codepoint '{}'", original),
            Token::String(s) => write!(f, "string \"{}\"", s),
            Token::Lident(s) => write!(f, "{}", s),
            Token::Uident(s) => write!(f, "{}", s),
            Token::Dot => write!(f, "."),
            Token::DotDot => write!(f, ".."),
            Token::DotDotDot => write!(f, "..."),
            Token::Int { i, .. } => write!(f, "int {}", i),
            Token::Float { f: fl, .. } => write!(f, "Float: {}", fl),
            Token::Bang => write!(f, "!"),
            Token::Semicolon => write!(f, ";"),
            Token::Let { unwrap: true } => write!(f, "let?"),
            Token::Let { unwrap: false } => write!(f, "let"),
            Token::And => write!(f, "and"),
            Token::Rec => write!(f, "rec"),
            Token::Underscore => write!(f, "_"),
            Token::SingleQuote => write!(f, "'"),
            Token::Equal => write!(f, "="),
            Token::EqualEqual => write!(f, "=="),
            Token::EqualEqualEqual => write!(f, "==="),
            Token::Eof => write!(f, "eof"),
            Token::Ampersand => write!(f, "&"),
            Token::Bar => write!(f, "|"),
            Token::As => write!(f, "as"),
            Token::Lparen => write!(f, "("),
            Token::Rparen => write!(f, ")"),
            Token::Lbracket => write!(f, "["),
            Token::Rbracket => write!(f, "]"),
            Token::Lbrace => write!(f, "{{"),
            Token::Rbrace => write!(f, "}}"),
            Token::ColonGreaterThan => write!(f, ":>"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Minus => write!(f, "-"),
            Token::MinusDot => write!(f, "-."),
            Token::Plus => write!(f, "+"),
            Token::PlusDot => write!(f, "+."),
            Token::PlusPlus => write!(f, "++"),
            Token::PlusEqual => write!(f, "+="),
            Token::Regex { pattern, flags } => write!(f, "regex: /{}/{}", pattern, flags),
            Token::Forwardslash => write!(f, "/"),
            Token::ForwardslashDot => write!(f, "/."),
            Token::Exception => write!(f, "exception"),
            Token::Hash => write!(f, "#"),
            Token::HashEqual => write!(f, "#="),
            Token::GreaterThan => write!(f, ">"),
            Token::LessThan => write!(f, "<"),
            Token::Asterisk => write!(f, "*"),
            Token::AsteriskDot => write!(f, "*."),
            Token::Exponentiation => write!(f, "**"),
            Token::Assert => write!(f, "assert"),
            Token::Tilde => write!(f, "~"),
            Token::Question => write!(f, "?"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::For => write!(f, "for"),
            Token::In => write!(f, "in"),
            Token::While => write!(f, "while"),
            Token::Switch => write!(f, "switch"),
            Token::When => write!(f, "when"),
            Token::EqualGreater => write!(f, "=>"),
            Token::MinusGreater => write!(f, "->"),
            Token::External => write!(f, "external"),
            Token::Typ => write!(f, "type"),
            Token::Private => write!(f, "private"),
            Token::Constraint => write!(f, "constraint"),
            Token::Mutable => write!(f, "mutable"),
            Token::Include => write!(f, "include"),
            Token::Module => write!(f, "module"),
            Token::Of => write!(f, "of"),
            Token::Lor => write!(f, "||"),
            Token::Bnot => write!(f, "~~~"),
            Token::Bor => write!(f, "|||"),
            Token::Bxor => write!(f, "^^^"),
            Token::Band => write!(f, "&&&"),
            Token::Caret => write!(f, "^"),
            Token::Land => write!(f, "&&"),
            Token::BangEqual => write!(f, "!="),
            Token::BangEqualEqual => write!(f, "!=="),
            Token::GreaterEqual => write!(f, ">="),
            Token::LessEqual => write!(f, "<="),
            Token::ColonEqual => write!(f, ":="),
            Token::At => write!(f, "@"),
            Token::AtAt => write!(f, "@@"),
            Token::Percent => write!(f, "%"),
            Token::PercentPercent => write!(f, "%%"),
            Token::DollarLbrace => write!(f, "${{"),
            Token::Comment(c) => write!(f, "Comment{}", c),
            Token::List => write!(f, "list{{"),
            Token::Dict => write!(f, "dict{{"),
            Token::TemplatePart { text, .. } => write!(f, "{}${{", text),
            Token::TemplateTail { text, .. } => write!(f, "TemplateTail({})", text),
            Token::Backtick => write!(f, "`"),
            Token::Try => write!(f, "try"),
            Token::DocComment { content, .. } => write!(f, "DocComment {}", content),
            Token::ModuleComment { content, .. } => write!(f, "ModuleComment {}", content),
            Token::LeftShift => write!(f, "<<"),
            Token::RightShift => write!(f, ">>"),
            Token::RightShiftUnsigned => write!(f, ">>>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_precedence() {
        assert_eq!(Token::Lor.precedence(), 2);
        assert_eq!(Token::Land.precedence(), 3);
        assert_eq!(Token::Plus.precedence(), 9);
        assert_eq!(Token::Asterisk.precedence(), 10);
        assert_eq!(Token::Exponentiation.precedence(), 11);
        assert_eq!(Token::Dot.precedence(), 13);
        assert_eq!(Token::If.precedence(), 0);
    }

    #[test]
    fn test_is_keyword() {
        assert!(Token::If.is_keyword());
        assert!(Token::Let { unwrap: false }.is_keyword());
        assert!(Token::Let { unwrap: true }.is_keyword());
        assert!(!Token::Plus.is_keyword());
        assert!(!Token::<'_>::Lident(Cow::Borrowed("foo")).is_keyword());
    }

    #[test]
    fn test_lookup_keyword() {
        assert_eq!(Token::lookup_keyword("if"), Token::If);
        assert_eq!(Token::lookup_keyword("let"), Token::Let { unwrap: false });
        assert_eq!(Token::lookup_keyword("let?"), Token::Let { unwrap: true });
        assert_eq!(
            Token::lookup_keyword("Foo"),
            Token::Uident(Cow::Borrowed("Foo"))
        );
        assert_eq!(
            Token::lookup_keyword("foo"),
            Token::Lident(Cow::Borrowed("foo"))
        );
    }

    #[test]
    fn test_is_keyword_txt() {
        assert!(Token::is_keyword_txt("if"));
        assert!(Token::is_keyword_txt("let"));
        assert!(!Token::is_keyword_txt("foo"));
        assert!(!Token::is_keyword_txt("Foo"));
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Token::<'_>::If), "if");
        assert_eq!(format!("{}", Token::<'_>::Plus), "+");
        assert_eq!(format!("{}", Token::<'_>::EqualGreater), "=>");
        assert_eq!(
            format!(
                "{}",
                Token::Int {
                    i: Cow::Borrowed("42"),
                    suffix: None
                }
            ),
            "int 42"
        );
    }

    #[test]
    fn test_token_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Token<'static>>();
    }

    #[test]
    fn test_into_owned() {
        let borrowed: Token<'_> = Token::Lident(Cow::Borrowed("hello"));
        let owned: Token<'static> = borrowed.into_owned();
        assert_eq!(owned, Token::Lident(Cow::Owned("hello".to_string())));

        let keyword: Token<'_> = Token::If;
        let owned_kw: Token<'static> = keyword.into_owned();
        assert_eq!(owned_kw, Token::If);
    }
}
