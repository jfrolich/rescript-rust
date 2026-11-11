//! Warning types and warning configuration.
//!
//! [`Warning`] mirrors OCaml's `Warnings.t`; [`WarningConfig`] holds the
//! active/error state that OCaml keeps in the global `Warnings.current`
//! ref, so each compilation can carry its own copy.

use serde::{Deserialize, Serialize};
use std::fmt;

use crate::location::Location;

/// Warning types.
///
/// These correspond to `Warnings.t` in OCaml.
/// Warning numbers are preserved for compatibility.
/// Variant fields are internal representation matching the OCaml codebase.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(missing_docs)]
pub enum Warning {
    /// Warning 1: Suspicious-looking start-of-comment mark.
    CommentStart,
    /// Warning 2: Suspicious-looking end-of-comment mark.
    CommentNotEnd,
    /// Warning 3: Deprecated feature.
    Deprecated {
        message: String,
        def_loc: Location,
        use_loc: Location,
        can_be_automigrated: bool,
    },
    /// Warning 4: Fragile pattern matching.
    FragileMatch { typ: String },
    /// Warning 5: Partially applied function.
    PartialApplication,
    /// Warning 7: Method overridden.
    MethodOverride { methods: Vec<String> },
    /// Warning 8: Partial match (missing cases).
    PartialMatch { example: String },
    /// Warning 8: Partial match because every clause has a guard.
    AllClausesGuarded,
    /// Warning 9: Missing fields in record pattern.
    NonClosedRecordPattern { fields: String },
    /// Warning 10: Statement has non-unit type.
    StatementType,
    /// Warning 11: Unused match case.
    UnusedMatch { reason: String },
    /// Warning 12: Unused sub-pattern.
    UnusedPat { reason: String },
    /// Warning 14: Illegal backslash escape.
    IllegalBackslash,
    /// Warning 16: Unerasable optional argument.
    UnerasableOptionalArgument,
    /// Warning 20: Unused argument.
    UnusedArgument,
    /// Warning 21: Non-returning statement.
    NonreturningStatement,
    /// Warning 22: Preprocessor warning.
    Preprocessor { message: String },
    /// Warning 23: Useless record with clause.
    UselessRecordWith,
    /// Warning 26: Unused variable (let-bound or as-pattern).
    UnusedVariable { name: String },
    /// Warning 27: Unused variable (other).
    UnusedVariableStrict { name: String },
    /// Warning 28: Wildcard argument to constant constructor.
    WildcardArgToConstantConstr,
    /// Warning 29: End-of-line in string constant.
    EolInString,
    /// Warning 30: Duplicate definitions.
    DuplicateDefinitions {
        kind: String,
        name: String,
        type1: String,
        type2: String,
    },
    /// Warning 32: Unused value declaration.
    UnusedValueDeclaration { name: String },
    /// Warning 33: Unused open statement.
    UnusedOpen { name: String },
    /// Warning 34: Unused type declaration.
    UnusedTypeDeclaration { name: String },
    /// Warning 35: Unused for-loop index.
    UnusedForIndex { name: String },
    /// Warning 37: Unused constructor.
    UnusedConstructor {
        name: String,
        used_in_pattern: bool,
        is_private: bool,
    },
    /// Warning 38: Unused extension constructor.
    UnusedExtension {
        name: String,
        is_exception: bool,
        used_in_pattern: bool,
        is_private: bool,
    },
    /// Warning 39: Unused rec flag.
    UnusedRecFlag,
    /// Warning 41: Ambiguous name.
    AmbiguousName {
        names: Vec<String>,
        types: Vec<String>,
        is_label: bool,
    },
    /// Warning 43: Nonoptional label.
    NonoptionalLabel { name: String },
    /// Warning 44: Open shadows an identifier.
    OpenShadowIdentifier { kind: String, name: String },
    /// Warning 45: Open shadows a label or constructor.
    OpenShadowLabelConstructor { kind: String, name: String },
    /// Warning 47: Illegal attribute payload.
    AttributePayload { attr: String, message: String },
    /// Warning 48: Eliminated optional arguments.
    EliminatedOptionalArguments { args: Vec<String> },
    /// Warning 49: No cmi file found.
    NoCmiFile {
        name: String,
        reason: Option<String>,
    },
    /// Warning 52: Fragile literal pattern.
    FragileLiteralPattern,
    /// Warning 53: Misplaced attribute.
    MisplacedAttribute { name: String },
    /// Warning 54: Duplicated attribute.
    DuplicatedAttribute { name: String },
    /// Warning 56: Unreachable case.
    UnreachableCase,
    /// Warning 57: Ambiguous or-pattern variables.
    AmbiguousPattern { vars: Vec<String> },
    /// Warning 60: Unused module.
    UnusedModule { name: String },
    /// Warning 62: Type constraint on GADT type declaration.
    ConstraintOnGadt,
    /// Warning 101: Unused ReScript attribute.
    BsUnusedAttribute { name: String },
    /// Warning 102: Polymorphic comparison.
    BsPolymorphicComparison,
    /// Warning 103: FFI warning.
    BsFfiWarning { message: String },
    /// Warning 104: @deriving warning.
    BsDeriveWarning { message: String },
    /// Warning 105: Fragile external.
    BsFragileExternal { name: String },
    /// Warning 106: Unimplemented primitive.
    BsUnimplementedPrimitive { name: String },
    /// Warning 107: Integer literal overflow.
    BsIntegerLiteralOverflow,
    /// Warning 108: Uninterpreted delimiters.
    BsUninterpretedDelimiters { delim: String },
    /// Warning 109: Toplevel expression is not unit.
    BsToplevelExpressionUnit {
        return_type: Option<String>,
        is_function_call: bool,
    },
    /// Warning 110: Todo found.
    BsTodo { message: Option<String> },
    /// Warning 111: Mutation of a private record field.
    BsPrivateRecordMutation { field_name: String },
    /// Warning 112: record rest pattern overlaps an optional field.
    BsRecordRestOptionalOverlap { fields: Vec<String> },
}

impl Warning {
    /// Get the warning number.
    pub fn number(&self) -> i32 {
        match self {
            Warning::CommentStart => 1,
            Warning::CommentNotEnd => 2,
            Warning::Deprecated { .. } => 3,
            Warning::FragileMatch { .. } => 4,
            Warning::PartialApplication => 5,
            Warning::MethodOverride { .. } => 7,
            Warning::PartialMatch { .. } => 8,
            Warning::AllClausesGuarded => 8,
            Warning::NonClosedRecordPattern { .. } => 9,
            Warning::StatementType => 10,
            Warning::UnusedMatch { .. } => 11,
            Warning::UnusedPat { .. } => 12,
            Warning::IllegalBackslash => 14,
            Warning::UnerasableOptionalArgument => 16,
            Warning::UnusedArgument => 20,
            Warning::NonreturningStatement => 21,
            Warning::Preprocessor { .. } => 22,
            Warning::UselessRecordWith => 23,
            Warning::UnusedVariable { .. } => 26,
            Warning::UnusedVariableStrict { .. } => 27,
            Warning::WildcardArgToConstantConstr => 28,
            Warning::EolInString => 29,
            Warning::DuplicateDefinitions { .. } => 30,
            Warning::UnusedValueDeclaration { .. } => 32,
            Warning::UnusedOpen { .. } => 33,
            Warning::UnusedTypeDeclaration { .. } => 34,
            Warning::UnusedForIndex { .. } => 35,
            Warning::UnusedConstructor { .. } => 37,
            Warning::UnusedExtension { .. } => 38,
            Warning::UnusedRecFlag => 39,
            Warning::AmbiguousName { .. } => 41,
            Warning::NonoptionalLabel { .. } => 43,
            Warning::OpenShadowIdentifier { .. } => 44,
            Warning::OpenShadowLabelConstructor { .. } => 45,
            Warning::AttributePayload { .. } => 47,
            Warning::EliminatedOptionalArguments { .. } => 48,
            Warning::NoCmiFile { .. } => 49,
            Warning::FragileLiteralPattern => 52,
            Warning::MisplacedAttribute { .. } => 53,
            Warning::DuplicatedAttribute { .. } => 54,
            Warning::UnreachableCase => 56,
            Warning::AmbiguousPattern { .. } => 57,
            Warning::UnusedModule { .. } => 60,
            Warning::ConstraintOnGadt => 62,
            Warning::BsUnusedAttribute { .. } => 101,
            Warning::BsPolymorphicComparison => 102,
            Warning::BsFfiWarning { .. } => 103,
            Warning::BsDeriveWarning { .. } => 104,
            Warning::BsFragileExternal { .. } => 105,
            Warning::BsUnimplementedPrimitive { .. } => 106,
            Warning::BsIntegerLiteralOverflow => 107,
            Warning::BsUninterpretedDelimiters { .. } => 108,
            Warning::BsToplevelExpressionUnit { .. } => 109,
            Warning::BsTodo { .. } => 110,
            Warning::BsPrivateRecordMutation { .. } => 111,
            Warning::BsRecordRestOptionalOverlap { .. } => 112,
        }
    }

    /// Get the warning message.
    pub fn message(&self) -> String {
        match self {
            Warning::CommentStart => "this is the start of a comment.".to_string(),
            Warning::CommentNotEnd => "this is not the end of a comment.".to_string(),
            Warning::Deprecated {
                message,
                can_be_automigrated,
                ..
            } => {
                let mut msg = format!("deprecated: {message}");
                if *can_be_automigrated {
                    msg.push_str(
                        "\n\n  This can be automatically migrated by the ReScript migration tool. Run `rescript-tools migrate-all <project-root>` to run all automatic migrations available in your project, or `rescript-tools migrate <file>` to migrate a single file.",
                    );
                }
                msg
            }
            Warning::FragileMatch { typ } if typ.is_empty() => {
                "this pattern-matching is fragile.".to_string()
            }
            Warning::FragileMatch { typ } => {
                format!(
                    "this pattern-matching is fragile.\n\
                     It will remain exhaustive when constructors are added to type {typ}."
                )
            }
            Warning::PartialApplication => {
                "this function application is partial,\nmaybe some arguments are missing."
                    .to_string()
            }
            Warning::MethodOverride { methods } if methods.len() == 1 => {
                format!("the method {} is overridden.", methods[0])
            }
            Warning::MethodOverride { methods } => {
                format!(
                    "the following methods are overridden by the class {}:\n {}",
                    methods[0],
                    methods[1..].join(" ")
                )
            }
            Warning::PartialMatch { example } if example.is_empty() => {
                "You forgot to handle a possible case here, though we don't have more \
                 information on the value."
                    .to_string()
            }
            Warning::PartialMatch { example } => {
                format!(
                    "You forgot to handle a possible case here, for example: \n{}",
                    example
                )
            }
            Warning::AllClausesGuarded => "this pattern-matching is not exhaustive.\n\
                 All clauses in this pattern-matching are guarded."
                .to_string(),
            Warning::NonClosedRecordPattern { fields } => {
                format!(
                    "the following labels are not bound in this record pattern: {}\n\
                     Either bind these labels explicitly or add ', _' to the pattern.",
                    fields
                )
            }
            Warning::StatementType => {
                "This expression returns a value, but you're not doing anything with it. \
                 If this is on purpose, wrap it with `ignore`."
                    .to_string()
            }
            Warning::UnusedMatch { reason } if reason.is_empty() => {
                "this match case is unused.".to_string()
            }
            Warning::UnusedMatch { reason } => format!("this match case is unused.\n{reason}"),
            Warning::UnusedPat { reason } if reason.is_empty() => {
                "this sub-pattern is unused.".to_string()
            }
            Warning::UnusedPat { reason } => format!("this sub-pattern is unused.\n{reason}"),
            Warning::IllegalBackslash => "illegal backslash escape in string.".to_string(),
            Warning::UnerasableOptionalArgument => {
                "This optional parameter in final position will, in practice, not be optional.\n\
                 Reorder the parameters so that at least one non-optional one is in final position."
                    .to_string()
            }
            Warning::UnusedArgument => {
                "this argument will not be used by the function.".to_string()
            }
            Warning::NonreturningStatement => {
                "This statement does not continue execution; following code is unreachable."
                    .to_string()
            }
            Warning::Preprocessor { message } => message.clone(),
            Warning::UselessRecordWith => {
                "All the fields are already explicitly listed in this record. \
                 You can remove the `...` spread."
                    .to_string()
            }
            Warning::UnusedVariable { name } | Warning::UnusedVariableStrict { name } => {
                // Match compiler/ext/warnings.ml:393-400.
                format!(
                    "unused variable {}.\n\n\
                     Fix this by:\n\
                     - Deleting the variable if it's not used anymore.\n\
                     - Prepending the variable name with `_` (like `_{}`) to ignore that the variable is unused.\n\
                     - Using the variable somewhere.",
                    name, name
                )
            }
            Warning::WildcardArgToConstantConstr => {
                "wildcard pattern given as argument to a constant constructor".to_string()
            }
            Warning::EolInString => {
                "unescaped end-of-line in a string constant (non-portable code)".to_string()
            }
            Warning::DuplicateDefinitions {
                kind,
                name,
                type1,
                type2,
            } => {
                format!(
                    "the {} {} is defined in both types {} and {}.",
                    kind, name, type1, type2
                )
            }
            Warning::UnusedValueDeclaration { name } => format!("unused value {}.", name),
            Warning::UnusedOpen { name } => format!("unused open {}.", name),
            Warning::UnusedTypeDeclaration { name } => format!("unused type {}.", name),
            Warning::UnusedForIndex { name } => format!("unused for-loop index {}.", name),
            Warning::UnusedConstructor {
                name,
                used_in_pattern,
                is_private,
            } => {
                if *used_in_pattern {
                    format!(
                        "constructor {} is never used to build values.\n(However, this constructor appears in patterns.)",
                        name
                    )
                } else if *is_private {
                    format!(
                        "constructor {} is never used to build values.\nIts type is exported as a private type.",
                        name
                    )
                } else {
                    format!("unused constructor {}.", name)
                }
            }
            Warning::UnusedExtension {
                name,
                is_exception,
                used_in_pattern,
                is_private,
            } => {
                let kind = if *is_exception {
                    "exception"
                } else {
                    "extension constructor"
                };
                if *used_in_pattern {
                    format!(
                        "{} {} is never used to build values.\n(However, this constructor appears in patterns.)",
                        kind, name
                    )
                } else if *is_private {
                    format!(
                        "{} {} is never used to build values.\nIt is exported or rebound as a private extension.",
                        kind, name
                    )
                } else {
                    format!("unused {} {}", kind, name)
                }
            }
            Warning::UnusedRecFlag => "unused rec flag.".to_string(),
            Warning::AmbiguousName {
                names,
                types,
                is_label,
            } => {
                if *is_label {
                    format!(
                        "these field labels belong to several types: {}\n\
The first one was selected. Disambiguate if this is wrong.",
                        types.join(" ")
                    )
                } else if names.len() == 1 {
                    format!(
                        "{} belongs to several types: {}\n\
The first one was selected. Disambiguate if this is wrong.",
                        names[0],
                        types.join(" ")
                    )
                } else {
                    "ambiguous name".to_string()
                }
            }
            Warning::NonoptionalLabel { name } => format!("the label {} is not optional.", name),
            Warning::OpenShadowIdentifier { kind, name } => {
                format!(
                    "this open statement shadows the {} identifier {} (which is later used)",
                    kind, name
                )
            }
            Warning::OpenShadowLabelConstructor { kind, name } => {
                format!(
                    "this open statement shadows the {} {} (which is later used)",
                    kind, name
                )
            }
            Warning::AttributePayload { attr, message } => {
                format!("illegal payload for attribute @{attr}.\n{message}")
            }
            Warning::EliminatedOptionalArguments { args } => {
                let plural = if args.len() == 1 { "" } else { "s" };
                format!(
                    "implicit elimination of optional argument{} {}",
                    plural,
                    args.join(", ")
                )
            }
            Warning::NoCmiFile { name, reason } => match reason {
                Some(msg) => format!(
                    "no valid cmi file was found in path for module {}. {}",
                    name, msg
                ),
                None => format!("no cmi file was found in path for module {}", name),
            },
            Warning::FragileLiteralPattern => "Code should not depend on the actual values of\n\
this constructor's arguments. They are only for information\n\
and may change in future versions."
                .to_string(),
            Warning::MisplacedAttribute { name } => {
                format!("the @{name} attribute cannot appear in this context")
            }
            Warning::DuplicatedAttribute { name } => {
                format!("the @{name} attribute is used more than once on this expression")
            }
            Warning::UnreachableCase => {
                "this match case is unreachable.\nConsider replacing it with a refutation case '<pat> -> .'"
                    .to_string()
            }
            Warning::AmbiguousPattern { vars } => {
                // warnings.ml:386-393: `List.sort String.compare vars`.
                let mut vars = vars.clone();
                vars.sort();
                let msg = if vars.len() == 1 {
                    format!("variable {}", vars[0])
                } else {
                    format!("variables {}", vars.join(", "))
                };
                format!(
                    "Ambiguous or-pattern variables under guard;\n\
                     {} may match different arguments.",
                    msg
                )
            }
            Warning::UnusedModule { name } => format!("unused module {}.", name),
            Warning::ConstraintOnGadt => {
                "Type constraints do not apply to GADT cases of variant types.".to_string()
            }
            Warning::BsUnusedAttribute { name } => {
                format!(
                    "Unused attribute: @{}\n\
                     This attribute has no effect here.\n\
                     For example, some attributes are only meaningful in externals.\n",
                    name
                )
            }
            Warning::BsPolymorphicComparison => {
                "Polymorphic comparison introduced (maybe unsafe)".to_string()
            }
            Warning::BsFfiWarning { message } => format!("FFI warning: {}", message),
            Warning::BsDeriveWarning { message } => format!("@deriving warning: {}", message),
            Warning::BsFragileExternal { name } => {
                format!(
                    "{}: using an empty string as a shorthand to infer the external's name \
                     from the value's name is dangerous when refactoring",
                    name
                )
            }
            Warning::BsUnimplementedPrimitive { name } => {
                format!("Unimplemented primitive used: {}", name)
            }
            Warning::BsIntegerLiteralOverflow => {
                "Integer literal exceeds the range of representable integers of type int"
                    .to_string()
            }
            Warning::BsUninterpretedDelimiters { delim } => {
                format!("Uninterpreted delimiters {}", delim)
            }
            Warning::BsToplevelExpressionUnit {
                return_type,
                is_function_call,
            } => {
                // Match compiler/ext/warnings.ml:507-533.
                let subject = if *is_function_call {
                    " function call "
                } else {
                    " "
                };
                let ret = return_type
                    .as_ref()
                    .map(|ret| format!("`{ret}`"))
                    .unwrap_or_else(|| "something that is not `unit`".to_string());
                let mut message = format!(
                    "This{}is at the top level and is expected to return `unit`. \
                     But it's returning {}.\n\n  \
                     In ReScript, anything at the top level must evaluate to `unit`. You \
                     can fix this by assigning the expression to a value, or piping it into \
                     the `ignore` function.",
                    subject, ret
                );
                if return_type.is_some() {
                    let help_text = if *is_function_call {
                        "yourFunctionCall()"
                    } else {
                        "yourExpression"
                    };
                    message.push_str(&format!(
                        "\n\n  Possible solutions:\n  \
                         - Assigning to a value that is then ignored: `let _ = {help_text}`\n  \
                         - Piping into the built-in ignore function to ignore the result: `{help_text}->ignore`"
                    ));
                }
                message
            }
            Warning::BsTodo { message } => {
                // Match compiler/ext/warnings.ml:535-541.
                let mut text = match message {
                    Some(text) => format!("Todo found: {}", text),
                    None => "Todo found.".to_string(),
                };
                text.push_str(
                    "\n\nThis code is not implemented yet and will crash at runtime. Make sure you implement this before running the code.",
                );
                text
            }
            Warning::BsPrivateRecordMutation { field_name } => {
                format!("Mutation of private record field {:?}.", field_name)
            }
            Warning::BsRecordRestOptionalOverlap { fields } => {
                // Match compiler/ext/warnings.ml:440-456.
                let field_list = fields
                    .iter()
                    .map(|field| format!("\n- {}", field))
                    .collect::<String>();
                let header = match fields.len() {
                    1 => "The following optional field appears in both the explicit pattern and the rest type:",
                    _ => "The following optional fields appear in both the explicit pattern and the rest type:",
                };
                let footer = match fields.len() {
                    1 => "\n\nIt will always be absent from the rest record.",
                    _ => "\n\nThey will always be absent from the rest record.",
                };
                format!("{}{}{}", header, field_list, footer)
            }
        }
    }
}

impl fmt::Display for Warning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message())
    }
}

/// Warning configuration.
///
/// Controls which warnings are active and which are treated as errors.
#[derive(Debug, Clone)]
pub struct WarningConfig {
    /// Which warnings are active (indexed by warning number).
    active: [bool; MAX_WARNING_NUMBER],
    /// Which warnings are errors (indexed by warning number).
    errors: [bool; MAX_WARNING_NUMBER],
    /// Whether warnings are disabled globally.
    disabled: bool,
}

const MAX_WARNING_NUMBER: usize = 113;

impl Default for WarningConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl WarningConfig {
    /// Create a new warning configuration with defaults.
    pub fn new() -> Self {
        let mut config = Self {
            active: [true; MAX_WARNING_NUMBER],
            errors: [false; MAX_WARNING_NUMBER],
            disabled: false,
        };
        // Match OCaml compiler/ext/bsc_warnings.ml:46-48. ReScript starts
        // from `+a-4-9-20-41-102` and warning-as-error `-a+5+101+109`;
        // later -w/-warn-error flags are layered on top by
        // Warnings.parse_options in compiler/ext/warnings.ml.
        config.parse("+a-4-9-20-41-102").ok();
        config.parse_as_error("-a+5+101+109").ok();
        config
    }

    /// Disable all warnings.
    pub fn disable_all(&mut self) {
        self.disabled = true;
    }

    /// Check if a warning is active.
    pub fn is_active(&self, warning: &Warning) -> bool {
        if self.disabled {
            return false;
        }
        let n = warning.number() as usize;
        n < self.active.len() && self.active[n]
    }

    /// Check if a warning is an error.
    pub fn is_error(&self, warning: &Warning) -> bool {
        if self.disabled {
            return false;
        }
        let n = warning.number() as usize;
        n < self.errors.len() && self.errors[n]
    }

    /// OCaml `Warnings.parse_options false` (compiler/ext/warnings.ml:250-254):
    /// the spec is applied to copies of the tables, which replace the current
    /// state only if the whole spec is well formed.
    pub fn parse(&mut self, spec: &str) -> Result<(), String> {
        self.parse_options(false, spec)
    }

    /// OCaml `Warnings.parse_options true`: `+n`/uppercase letters set the
    /// error flag, `-n`/lowercase letters clear it, `@n` enables the warning
    /// and marks it as an error.
    pub fn parse_as_error(&mut self, spec: &str) -> Result<(), String> {
        self.parse_options(true, spec)
    }

    fn parse_options(&mut self, errflag: bool, spec: &str) -> Result<(), String> {
        let mut error = self.errors;
        let mut active = self.active;
        parse_opt(&mut error, &mut active, errflag, spec.as_bytes())?;
        self.errors = error;
        self.active = active;
        Ok(())
    }
}

/// OCaml `Warnings.last_warning_number` (compiler/ext/warnings.ml:134).
const LAST_WARNING_NUMBER: usize = MAX_WARNING_NUMBER - 1;

/// OCaml `Warnings.parse_opt` (compiler/ext/warnings.ml:192-248). `flags` is
/// `error` when `errflag` is set and `active` otherwise.
fn parse_opt(
    error: &mut [bool],
    active: &mut [bool],
    errflag: bool,
    s: &[u8],
) -> Result<(), String> {
    #[derive(Clone, Copy)]
    enum Action {
        Set,
        Clear,
        SetAll,
    }
    let ill_formed = || Err("Ill-formed list of warnings".to_string());
    let mut apply = |action: Action, n: usize| {
        if n >= active.len() {
            return;
        }
        match action {
            Action::Set if errflag => error[n] = true,
            Action::Set => active[n] = true,
            Action::Clear if errflag => error[n] = false,
            Action::Clear => active[n] = false,
            Action::SetAll => {
                active[n] = true;
                error[n] = true;
            }
        }
    };
    let get_num = |mut i: usize| {
        let mut n = 0usize;
        while i < s.len() && s[i].is_ascii_digit() {
            n = n.saturating_mul(10).saturating_add((s[i] - b'0') as usize);
            i += 1;
        }
        (i, n)
    };
    let mut i = 0;
    while i < s.len() {
        let action = match s[i] {
            c @ b'A'..=b'Z' => {
                for &n in letter_warnings(c.to_ascii_lowercase() as char) {
                    apply(Action::Set, n);
                }
                i += 1;
                continue;
            }
            c @ b'a'..=b'z' => {
                for &n in letter_warnings(c as char) {
                    apply(Action::Clear, n);
                }
                i += 1;
                continue;
            }
            b'+' => Action::Set,
            b'-' => Action::Clear,
            b'@' => Action::SetAll,
            _ => return ill_formed(),
        };
        // loop_letter_num
        i += 1;
        if i >= s.len() {
            return ill_formed();
        }
        match s[i] {
            b'0'..=b'9' => {
                let (next, n1) = get_num(i);
                let (next, n2) = if next + 2 < s.len() && s[next] == b'.' && s[next + 1] == b'.' {
                    let (next, n2) = get_num(next + 2);
                    if n2 < n1 {
                        return ill_formed();
                    }
                    (next, n2)
                } else {
                    (next, n1)
                };
                let mut n = n1;
                while n <= n2.min(LAST_WARNING_NUMBER) {
                    apply(action, n);
                    n += 1;
                }
                i = next;
            }
            c @ (b'A'..=b'Z' | b'a'..=b'z') => {
                for &n in letter_warnings(c.to_ascii_lowercase() as char) {
                    apply(action, n);
                }
                i += 1;
            }
            _ => return ill_formed(),
        }
    }
    Ok(())
}

/// Warning numbers 1..=LAST_WARNING_NUMBER, for the letter `a`.
const ALL_WARNINGS: [usize; LAST_WARNING_NUMBER] = {
    let mut all = [0; LAST_WARNING_NUMBER];
    let mut i = 0;
    while i < LAST_WARNING_NUMBER {
        all[i] = i + 1;
        i += 1;
    }
    all
};

/// Get warning numbers for a letter abbreviation.
fn letter_warnings(letter: char) -> &'static [usize] {
    match letter {
        'a' => &ALL_WARNINGS,
        'c' => &[],
        'd' => &[3],
        'e' => &[4],
        'f' => &[5],
        'k' => &[32, 33, 34, 35, 37, 38, 39],
        'l' => &[],
        'm' => &[],
        'p' => &[8],
        'r' => &[9],
        's' => &[],
        'u' => &[11, 12],
        'v' => &[],
        'x' => &[20, 21, 22, 23, 30],
        'y' => &[26],
        'z' => &[27],
        _ => &[],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_warning_number() {
        assert_eq!(Warning::CommentStart.number(), 1);
        assert_eq!(
            Warning::UnusedVariable {
                name: "x".to_string()
            }
            .number(),
            26
        );
        assert_eq!(Warning::BsTodo { message: None }.number(), 110);
        assert_eq!(
            Warning::BsPrivateRecordMutation {
                field_name: "value".to_string()
            }
            .number(),
            111
        );
    }

    #[test]
    fn test_warning_config_parse() {
        let mut config = WarningConfig::new();
        config.parse("+1-2@3").unwrap();

        assert!(config.active[1]);
        assert!(!config.active[2]);
        assert!(config.active[3]);
        assert!(config.errors[3]);
    }

    #[test]
    fn test_warning_config_parse_as_error() {
        let mut config = WarningConfig::new();
        config.parse("-26").unwrap();
        config.parse_as_error("+26").unwrap();

        assert!(!config.active[26]);
        assert!(config.errors[26]);

        config.parse_as_error("-26").unwrap();

        assert!(!config.active[26]);
        assert!(!config.errors[26]);

        config.parse_as_error("@26").unwrap();

        assert!(config.active[26]);
        assert!(config.errors[26]);
    }

    #[test]
    fn test_warning_config_range() {
        let mut config = WarningConfig::new();
        config.parse("-1..10").unwrap();

        assert!(config.active[1..=10].iter().all(|active| !active));
    }
}
