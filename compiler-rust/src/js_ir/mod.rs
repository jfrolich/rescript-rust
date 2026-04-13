//! JavaScript IR - Intermediate representation for JavaScript output.
//!
//! This module provides the JavaScript IR, which is the final intermediate
//! representation before generating JavaScript source code. It's a subset
//! of JavaScript AST specialized for the ReScript compilation target.
//!
//! # Architecture
//!
//! The JS IR is organized into:
//!
//! - [`op`] - Operators, properties, and other JS-specific types
//! - Expressions - Values that produce results
//! - Statements - Instructions that have effects
//! - Programs - Complete compilation units

pub mod op;
pub mod printer;

use std::ffi::OsString;
use std::path::{Component, Path as FsPath, PathBuf};

use crate::cmi::persistent_env::PersistentEnv;
use crate::ident::Ident;
use crate::lambda::tag_info::TagInfo;
pub use op::{BinOp, IdentInfo, Kind, LengthObject, MutableFlag, Number, Property, PropertyName};
pub use printer::{JsPrinter, print_block, print_deps_program, print_expression, print_program};

/// Module identifier for imports/requires
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuleId {
    /// The module identifier
    pub id: Ident,
    /// Module kind (Ml, Runtime, External)
    pub kind: Kind,
    /// Is this a dynamic import?
    pub dynamic_import: bool,
}

/// Output module format used to resolve import paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleFormat {
    /// ECMAScript modules (`.mjs`)
    EsModule,
    /// CommonJS (`.js`, `.bs.js`)
    CommonJs,
}

/// Resolves lowered module identifiers to emitted JavaScript import paths.
#[derive(Clone)]
pub struct ModulePathResolver {
    format: ModuleFormat,
    output_suffix: String,
    current_source_path: Option<PathBuf>,
    runtime_path: Option<PathBuf>,
    persistent_env: Option<PersistentEnv>,
}

impl ModulePathResolver {
    /// Build a resolver from the current compilation context.
    pub fn from_compile_options(
        source_filename: Option<&str>,
        output_path: Option<&FsPath>,
        runtime_path: Option<&FsPath>,
        persistent_env: Option<PersistentEnv>,
    ) -> Self {
        Self {
            format: module_format_from_output_path(output_path),
            output_suffix: output_suffix_from_path(output_path),
            current_source_path: source_filename
                .map(|path| normalize_absolute_path(FsPath::new(path))),
            runtime_path: runtime_path.map(normalize_absolute_path),
            persistent_env,
        }
    }

    /// Resolve the emitted JavaScript import path for a lowered module id.
    pub fn resolve_module_path(&self, module: &ModuleId) -> Option<String> {
        match &module.kind {
            Kind::External { name, .. } => Some(name.clone()),
            Kind::Runtime => Some(self.runtime_module_path(module.id.name())),
            Kind::Ml => {
                if self.is_runtime_module(module.id.name()) {
                    Some(self.runtime_module_path(module.id.name()))
                } else {
                    let target_source = self
                        .persistent_env
                        .as_ref()?
                        .resolve_module_source_path(module.id.name())
                        .map(|path| normalize_absolute_path(&path))?;
                    self.relative_output_path(&target_source)
                }
            }
        }
    }

    /// Return the side-effect reason OCaml records for a required module, if it
    /// is not marked pure.
    pub fn module_side_effect_reason(&self, module: &ModuleId) -> Option<String> {
        if self.is_pure_module(module) {
            return None;
        }

        Some(match &module.kind {
            Kind::External { name, .. } => name.clone(),
            Kind::Runtime | Kind::Ml => module.id.name().to_string(),
        })
    }

    fn runtime_module_path(&self, module_name: &str) -> String {
        let dir = match self.format {
            ModuleFormat::EsModule => "es6",
            ModuleFormat::CommonJs => "js",
        };
        format!("@rescript/runtime/lib/{dir}/{module_name}.js")
    }

    fn is_runtime_module(&self, module_name: &str) -> bool {
        let Some(runtime_path) = &self.runtime_path else {
            return false;
        };
        let ocaml_dir = runtime_path.join("lib").join("ocaml");
        ocaml_dir.join(format!("{module_name}.cmi")).exists()
            || ocaml_dir.join(format!("{module_name}.ast")).exists()
            || ocaml_dir.join(format!("{module_name}.iast")).exists()
    }

    fn is_pure_module(&self, module: &ModuleId) -> bool {
        match &module.kind {
            Kind::Runtime => true,
            Kind::External { .. } => false,
            Kind::Ml => {
                if self.is_runtime_module(module.id.name()) {
                    true
                } else {
                    self.persistent_env
                        .as_ref()
                        .and_then(|env| env.module_cmj_is_pure(module.id.name()))
                        .unwrap_or(false)
                }
            }
        }
    }

    fn relative_output_path(&self, target_source: &FsPath) -> Option<String> {
        let current_source = self.current_source_path.as_ref()?;
        let from_dir = current_source.parent()?;
        let target_dir = target_source.parent()?;
        let target_stem = target_source.file_stem()?.to_str()?;
        let target_output = target_dir.join(format!("{target_stem}{}", self.output_suffix));
        let relative = relative_path_between(from_dir, &target_output)?;
        let mut rendered = relative.to_string_lossy().replace('\\', "/");
        if !rendered.starts_with("./") && !rendered.starts_with("../") {
            rendered = format!("./{rendered}");
        }
        Some(rendered)
    }
}

fn module_format_from_output_path(output_path: Option<&FsPath>) -> ModuleFormat {
    match output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
    {
        Some(name) if name.ends_with(".mjs") => ModuleFormat::EsModule,
        _ => ModuleFormat::CommonJs,
    }
}

fn output_suffix_from_path(output_path: Option<&FsPath>) -> String {
    match output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
    {
        Some(name) if name.ends_with(".mjs") => ".mjs".to_string(),
        Some(name) if name.ends_with(".bs.js") => ".bs.js".to_string(),
        _ => ".js".to_string(),
    }
}

fn normalize_absolute_path(path: &FsPath) -> PathBuf {
    let base = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    };
    normalize_lexical_path(base)
}

fn normalize_lexical_path(path: PathBuf) -> PathBuf {
    let mut prefix: Option<OsString> = None;
    let mut has_root = false;
    let mut parts: Vec<OsString> = Vec::new();

    for component in path.components() {
        match component {
            Component::Prefix(value) => prefix = Some(value.as_os_str().to_os_string()),
            Component::RootDir => has_root = true,
            Component::CurDir => {}
            Component::ParentDir => match parts.last() {
                Some(last) if last != ".." => {
                    parts.pop();
                }
                _ if !has_root && prefix.is_none() => parts.push(OsString::from("..")),
                _ => {}
            },
            Component::Normal(part) => parts.push(part.to_os_string()),
        }
    }

    let mut normalized = PathBuf::new();
    if let Some(prefix) = prefix {
        normalized.push(prefix);
    }
    if has_root {
        normalized.push(std::path::MAIN_SEPARATOR.to_string());
    }
    for part in parts {
        normalized.push(part);
    }

    if normalized.as_os_str().is_empty() && !has_root {
        PathBuf::from(".")
    } else {
        normalized
    }
}

fn relative_path_between(base_dir: &FsPath, target: &FsPath) -> Option<PathBuf> {
    let base = normalize_lexical_path(base_dir.to_path_buf());
    let target = normalize_lexical_path(target.to_path_buf());

    let base_components: Vec<_> = base.components().collect();
    let target_components: Vec<_> = target.components().collect();

    if matches!(
        (base_components.first(), target_components.first()),
        (Some(Component::Prefix(left)), Some(Component::Prefix(right)))
            if left.as_os_str() != right.as_os_str()
    ) {
        return None;
    }

    let shared_prefix = base_components
        .iter()
        .zip(target_components.iter())
        .take_while(|(left, right)| left == right)
        .count();

    let mut relative = PathBuf::new();
    for component in &base_components[shared_prefix..] {
        if matches!(component, Component::Normal(_)) {
            relative.push("..");
        }
    }
    for component in &target_components[shared_prefix..] {
        match component {
            Component::Normal(part) => relative.push(part),
            Component::CurDir => {}
            Component::ParentDir => relative.push(".."),
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }

    Some(relative)
}

/// Variable identifier (local or qualified)
#[derive(Debug, Clone, PartialEq)]
pub enum VIdent {
    /// Local identifier
    Id(Ident),
    /// Qualified identifier (module.member)
    Qualified(ModuleId, Option<String>),
}

/// String delimiter type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delim {
    /// No special delimiter
    None,
    /// StarJ format
    StarJ,
    /// No quotes (raw)
    NoQuotes,
    /// Backtick template literal
    BackQuotes,
}

/// For loop direction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForDirection {
    /// i++
    Upto,
    /// i--
    Downto,
    /// for...of style
    Up,
}

/// Call information for function calls
#[derive(Debug, Clone, Default)]
pub struct CallInfo {
    /// Is this a method call?
    pub is_method: bool,
    /// Additional metadata
    pub comment: Option<String>,
}

/// Function environment (for closures)
#[derive(Debug, Clone, Default)]
pub struct FunEnv {
    /// Captured variables
    pub captured: Vec<Ident>,
}

/// Raw JavaScript code info
#[derive(Debug, Clone, PartialEq)]
pub struct JsRawInfo {
    /// The JavaScript code
    pub code: String,
    /// Is this a statement?
    pub is_stmt: bool,
}

/// JavaScript expression description
#[derive(Debug, Clone)]
pub enum ExpressionDesc {
    /// Length property access (arr.length, str.length)
    Length(Box<Expression>, LengthObject),

    /// Null/undefined check (== null)
    IsNullOrUndefined(Box<Expression>),

    /// String concatenation
    StringAppend(Box<Expression>, Box<Expression>),

    /// Boolean literal
    Bool(bool),

    /// typeof operator
    Typeof(Box<Expression>),

    /// in operator (prop in obj)
    In(Box<Expression>, Box<Expression>),

    /// Logical not (!)
    JsNot(Box<Expression>),

    /// Bitwise not (~)
    JsBnot(Box<Expression>),

    /// Sequence expression (a, b)
    Seq(Box<Expression>, Box<Expression>),

    /// Conditional expression (a ? b : c)
    Cond(Box<Expression>, Box<Expression>, Box<Expression>),

    /// Binary operation
    Bin(BinOp, Box<Expression>, Box<Expression>),

    /// Function.prototype.apply call
    FlatCall(Box<Expression>, Box<Expression>),

    /// Function call
    Call(Box<Expression>, Vec<Expression>, CallInfo),

    /// String index access (str[i])
    StringIndex(Box<Expression>, Box<Expression>),

    /// Array index access (arr[i])
    ArrayIndex(Box<Expression>, Box<Expression>),

    /// Tagged template literal
    TaggedTemplate(Box<Expression>, Vec<Expression>, Vec<Expression>),

    /// Static property access (obj.prop or obj["prop"])
    StaticIndex(Box<Expression>, String, Option<i32>),

    /// new expression
    New(Box<Expression>, Option<Vec<Expression>>),

    /// Variable reference
    Var(VIdent),

    /// Function expression
    Fun {
        is_method: bool,
        params: Vec<Ident>,
        body: Block,
        env: FunEnv,
        return_unit: bool,
        async_: bool,
        directive: Option<String>,
    },

    /// String literal
    Str { delim: Delim, txt: String },

    /// Raw JavaScript code
    RawJsCode(JsRawInfo),

    /// Array literal
    Array(Vec<Expression>, MutableFlag),

    /// Optional block (Some value)
    OptionalBlock(Box<Expression>, bool),

    /// Caml block (variant, record, tuple)
    CamlBlock(Vec<Expression>, MutableFlag, Box<Expression>, TagInfo),

    /// Block tag access
    CamlBlockTag(Box<Expression>, String),

    /// Number literal
    Number(Number),

    /// Object literal
    Object(Option<Box<Expression>>, PropertyMap),

    /// undefined literal
    Undefined { is_unit: bool },

    /// null literal
    Null,

    /// await expression
    Await(Box<Expression>),

    /// spread operator
    Spread(Box<Expression>),
}

/// Property map for object literals
pub type PropertyMap = Vec<(PropertyName, Expression)>;

/// JavaScript expression
#[derive(Debug, Clone)]
pub struct Expression {
    /// Expression description
    pub desc: ExpressionDesc,
    /// Optional comment
    pub comment: Option<String>,
}

impl Expression {
    /// Create a new expression
    pub fn new(desc: ExpressionDesc) -> Self {
        Self {
            desc,
            comment: None,
        }
    }

    /// Create a new expression with a comment
    pub fn with_comment(desc: ExpressionDesc, comment: impl Into<String>) -> Self {
        Self {
            desc,
            comment: Some(comment.into()),
        }
    }

    /// Create a boolean expression
    pub fn bool(value: bool) -> Self {
        Self::new(ExpressionDesc::Bool(value))
    }

    /// Create a variable expression
    pub fn var(id: Ident) -> Self {
        Self::new(ExpressionDesc::Var(VIdent::Id(id)))
    }

    /// Create a qualified variable expression
    pub fn qualified(module: ModuleId, member: Option<String>) -> Self {
        Self::new(ExpressionDesc::Var(VIdent::Qualified(module, member)))
    }

    /// Create a string expression
    pub fn string(txt: impl Into<String>) -> Self {
        Self::new(ExpressionDesc::Str {
            delim: Delim::None,
            txt: txt.into(),
        })
    }

    /// Create an undefined expression
    pub fn undefined(is_unit: bool) -> Self {
        Self::new(ExpressionDesc::Undefined { is_unit })
    }

    /// Create a null expression
    pub fn null() -> Self {
        Self::new(ExpressionDesc::Null)
    }

    /// Create a number expression
    pub fn number(n: Number) -> Self {
        Self::new(ExpressionDesc::Number(n))
    }

    /// Create an array expression
    pub fn array(elements: Vec<Expression>, mutable_flag: MutableFlag) -> Self {
        Self::new(ExpressionDesc::Array(elements, mutable_flag))
    }

    /// Create a binary operation
    pub fn bin(op: BinOp, left: Expression, right: Expression) -> Self {
        Self::new(ExpressionDesc::Bin(op, Box::new(left), Box::new(right)))
    }

    /// Create a function call
    pub fn call(func: Expression, args: Vec<Expression>, info: CallInfo) -> Self {
        Self::new(ExpressionDesc::Call(Box::new(func), args, info))
    }

    /// Create a conditional expression
    pub fn cond(test: Expression, consequent: Expression, alternate: Expression) -> Self {
        Self::new(ExpressionDesc::Cond(
            Box::new(test),
            Box::new(consequent),
            Box::new(alternate),
        ))
    }

    /// Create a negated boolean expression, mirroring OCaml `Js_exp_make.not`.
    pub fn not(expr: Expression) -> Self {
        let Expression { desc, comment } = expr;
        match desc {
            ExpressionDesc::Number(Number::Int { i, .. }) => Expression {
                desc: ExpressionDesc::Bool(i == 0),
                comment,
            },
            ExpressionDesc::JsNot(inner) => *inner,
            ExpressionDesc::Bool(value) => Expression {
                desc: ExpressionDesc::Bool(!value),
                comment,
            },
            ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::NotEqEq, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::NotEqEq, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::EqEqEq, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Lt, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Ge, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Ge, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Lt, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Le, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Gt, left, right),
                comment,
            },
            ExpressionDesc::Bin(BinOp::Gt, left, right) => Expression {
                desc: ExpressionDesc::Bin(BinOp::Le, left, right),
                comment,
            },
            other => {
                let expr = Expression {
                    desc: other,
                    comment,
                };
                push_negation(expr.clone()).unwrap_or_else(|| Expression {
                    desc: ExpressionDesc::JsNot(Box::new(expr)),
                    comment: None,
                })
            }
        }
    }
}

fn push_negation(expr: Expression) -> Option<Expression> {
    let Expression { desc, comment } = expr;
    match desc {
        ExpressionDesc::JsNot(inner) => Some(*inner),
        ExpressionDesc::Bool(value) => Some(Expression {
            desc: ExpressionDesc::Bool(!value),
            comment,
        }),
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => Some(Expression {
            desc: ExpressionDesc::Bin(BinOp::NotEqEq, left, right),
            comment,
        }),
        ExpressionDesc::Bin(BinOp::NotEqEq, left, right) => Some(Expression {
            desc: ExpressionDesc::Bin(BinOp::EqEqEq, left, right),
            comment,
        }),
        ExpressionDesc::Bin(BinOp::And, left, right) => {
            let left = push_negation(*left)?;
            let right = push_negation(*right)?;
            Some(Expression {
                desc: ExpressionDesc::Bin(BinOp::Or, Box::new(left), Box::new(right)),
                comment,
            })
        }
        ExpressionDesc::Bin(BinOp::Or, left, right) => {
            let left = push_negation(*left)?;
            let right = push_negation(*right)?;
            Some(Expression {
                desc: ExpressionDesc::Bin(BinOp::And, Box::new(left), Box::new(right)),
                comment,
            })
        }
        _ => None,
    }
}

/// Switch case clause
#[derive(Debug, Clone)]
pub struct CaseClause {
    /// Case body
    pub body: Block,
    /// Should break after this case?
    pub should_break: bool,
    /// Optional comment
    pub comment: Option<String>,
}

/// Integer switch clause
pub type IntClause = (i32, CaseClause);

/// String switch clause (tag type, case clause)
#[derive(Debug, Clone)]
pub struct StringClause {
    /// Tag type (from Ast_untagged_variants)
    pub tag_type: String,
    /// Case clause
    pub clause: CaseClause,
}

/// Variable declaration
#[derive(Debug, Clone)]
pub struct VariableDeclaration {
    /// Variable identifier
    pub ident: Ident,
    /// Initial value
    pub value: Option<Expression>,
    /// Declaration property (let, const, var semantics)
    pub property: Property,
    /// Usage info
    pub ident_info: IdentInfo,
}

/// JavaScript statement description
#[derive(Debug, Clone)]
pub enum StatementDesc {
    /// Block of statements
    Block(Block),

    /// Variable declaration
    Variable(VariableDeclaration),

    /// Expression statement
    Exp(Expression),

    /// If statement
    If(Expression, Block, Block),

    /// While loop
    While(Expression, Block),

    /// For loop (init, end, ident, direction, body)
    ForRange(Option<Expression>, Expression, Ident, ForDirection, Block),

    /// Continue statement
    Continue,

    /// Break statement
    Break,

    /// Return statement
    Return(Expression),

    /// Integer switch
    IntSwitch(Expression, Vec<IntClause>, Option<Block>),

    /// String switch
    StringSwitch(Expression, Vec<StringClause>, Option<Block>),

    /// Throw statement
    Throw(Expression),

    /// Try statement (body, catch, finally)
    Try(Block, Option<(Ident, Block)>, Option<Block>),

    /// Debugger statement
    Debugger,
}

/// JavaScript statement
#[derive(Debug, Clone)]
pub struct Statement {
    /// Statement description
    pub desc: StatementDesc,
    /// Optional comment
    pub comment: Option<String>,
}

impl Statement {
    /// Create a new statement
    pub fn new(desc: StatementDesc) -> Self {
        Self {
            desc,
            comment: None,
        }
    }

    /// Create a new statement with a comment
    pub fn with_comment(desc: StatementDesc, comment: impl Into<String>) -> Self {
        Self {
            desc,
            comment: Some(comment.into()),
        }
    }

    /// Create an expression statement
    pub fn exp(expr: Expression) -> Self {
        Self::new(StatementDesc::Exp(expr))
    }

    /// Create an if statement
    pub fn if_(cond: Expression, then_: Block, else_: Block) -> Self {
        simplify_if_statement(cond, then_, else_)
    }

    /// Create a while loop
    pub fn while_(cond: Expression, body: Block) -> Self {
        Self::new(StatementDesc::While(cond, body))
    }

    /// Create a return statement
    pub fn return_(expr: Expression) -> Self {
        Self::new(StatementDesc::Return(expr))
    }

    /// Create a throw statement
    pub fn throw(expr: Expression) -> Self {
        Self::new(StatementDesc::Throw(expr))
    }

    /// Create a break statement
    pub fn break_() -> Self {
        Self::new(StatementDesc::Break)
    }

    /// Create a continue statement
    pub fn continue_() -> Self {
        Self::new(StatementDesc::Continue)
    }

    /// Create a debugger statement
    pub fn debugger() -> Self {
        Self::new(StatementDesc::Debugger)
    }

    /// Create a variable declaration
    pub fn variable(decl: VariableDeclaration) -> Self {
        Self::new(StatementDesc::Variable(decl))
    }
}

fn simplify_if_statement(cond: Expression, then_: Block, else_: Block) -> Statement {
    match cond.desc {
        ExpressionDesc::Bool(value) => {
            return Statement::new(StatementDesc::Block(if value {
                then_
            } else {
                else_
            }))
        }
        ExpressionDesc::JsNot(inner) if !else_.is_empty() => {
            return simplify_if_statement(*inner, else_, then_);
        }
        _ => {}
    }

    if then_.is_empty() {
        if else_.is_empty() {
            return Statement::exp(cond);
        }
        return simplify_if_statement(negate_condition(cond), else_, vec![]);
    }

    if let (Some(then_ret), Some(else_ret)) = (single_return_expr(&then_), single_return_expr(&else_)) {
        return Statement::return_(Expression::cond(cond, then_ret, else_ret));
    }

    if let Some(else_ret) = single_return_expr(&else_) {
        let mut block = Vec::with_capacity(1 + then_.len());
        block.push(Statement::new(StatementDesc::If(
            negate_condition(cond),
            vec![Statement::return_(else_ret)],
            vec![],
        )));
        block.extend(then_);
        return Statement::new(StatementDesc::Block(block));
    }

    if block_last_is_terminal(&then_) {
        let mut block = Vec::with_capacity(1 + else_.len());
        block.push(Statement::new(StatementDesc::If(cond, then_, vec![])));
        block.extend(else_);
        return Statement::new(StatementDesc::Block(block));
    }

    if let (Some((lhs_then, rhs_then)), Some((lhs_else, rhs_else))) =
        (single_assignment_expr(&then_), single_assignment_expr(&else_))
    {
        if same_assignment_target(&lhs_then, &lhs_else) {
            return Statement::exp(Expression::bin(
                BinOp::Eq,
                lhs_then,
                Expression::cond(cond, rhs_then, rhs_else),
            ));
        }
    }

    if let (Some(then_expr), Some(else_expr)) = (single_exp_expr(&then_), single_exp_expr(&else_)) {
        return Statement::exp(Expression::cond(cond, then_expr, else_expr));
    }

    Statement::new(StatementDesc::If(cond, then_, else_))
}

fn block_last_is_terminal(block: &Block) -> bool {
    matches!(
        block.last().map(|stmt| &stmt.desc),
        Some(StatementDesc::Return(_))
            | Some(StatementDesc::Throw(_))
            | Some(StatementDesc::Continue)
    )
}

fn single_return_expr(block: &Block) -> Option<Expression> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    match &stmt.desc {
        StatementDesc::Return(expr) => Some(expr.clone()),
        _ => None,
    }
}

fn single_assignment_expr(block: &Block) -> Option<(Expression, Expression)> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    let StatementDesc::Exp(expr) = &stmt.desc else {
        return None;
    };
    let ExpressionDesc::Bin(BinOp::Eq, lhs, rhs) = &expr.desc else {
        return None;
    };
    Some(((*lhs.clone()), (*rhs.clone())))
}

fn same_assignment_target(lhs: &Expression, rhs: &Expression) -> bool {
    match (&lhs.desc, &rhs.desc) {
        (ExpressionDesc::Var(left), ExpressionDesc::Var(right)) => left == right,
        (
            ExpressionDesc::StaticIndex(left_obj, left_field, left_pos),
            ExpressionDesc::StaticIndex(right_obj, right_field, right_pos),
        ) => {
            left_field == right_field
                && left_pos == right_pos
                && same_assignment_target(left_obj, right_obj)
        }
        (
            ExpressionDesc::ArrayIndex(left_obj, left_index),
            ExpressionDesc::ArrayIndex(right_obj, right_index),
        )
        | (
            ExpressionDesc::StringIndex(left_obj, left_index),
            ExpressionDesc::StringIndex(right_obj, right_index),
        ) => {
            same_assignment_target(left_obj, right_obj) && same_assignment_target(left_index, right_index)
        }
        _ => false,
    }
}

fn single_exp_expr(block: &Block) -> Option<Expression> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    let StatementDesc::Exp(expr) = &stmt.desc else {
        return None;
    };
    Some(expr.clone())
}

fn negate_condition(cond: Expression) -> Expression {
    Expression::not(cond)
}

/// Block of statements
pub type Block = Vec<Statement>;

/// Exports from a module
pub type Exports = Vec<Ident>;

/// Required (imported) modules
pub type RequiredModules = Vec<ModuleId>;

/// JavaScript program
#[derive(Debug, Clone)]
pub struct Program {
    /// Program statements
    pub block: Block,
    /// Exported identifiers
    pub exports: Exports,
    /// Set of exported identifiers
    pub export_set: std::collections::HashSet<Ident>,
}

impl Program {
    /// Create a new program
    pub fn new(block: Block, exports: Exports) -> Self {
        let export_set = exports.iter().cloned().collect();
        Self {
            block,
            exports,
            export_set,
        }
    }

    /// Create an empty program
    pub fn empty() -> Self {
        Self {
            block: vec![],
            exports: vec![],
            export_set: std::collections::HashSet::new(),
        }
    }
}

/// Program with dependencies
#[derive(Debug, Clone)]
pub struct DepsProgram {
    /// The program
    pub program: Program,
    /// Required modules
    pub modules: RequiredModules,
    /// Side effect reason (None = no side effects)
    pub side_effect: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expression_creation() {
        let expr = Expression::bool(true);
        match expr.desc {
            ExpressionDesc::Bool(true) => {}
            _ => panic!("Expected Bool(true)"),
        }
    }

    #[test]
    fn test_variable_expression() {
        let id = Ident::create_local("x");
        let expr = Expression::var(id.clone());
        match &expr.desc {
            ExpressionDesc::Var(VIdent::Id(i)) => {
                assert_eq!(i.name(), "x");
            }
            _ => panic!("Expected Var(Id)"),
        }
    }

    #[test]
    fn test_string_expression() {
        let expr = Expression::string("hello");
        match &expr.desc {
            ExpressionDesc::Str {
                delim: Delim::None,
                txt,
            } => {
                assert_eq!(txt, "hello");
            }
            _ => panic!("Expected Str"),
        }
    }

    #[test]
    fn test_binary_expression() {
        let left = Expression::number(Number::int(1));
        let right = Expression::number(Number::int(2));
        let expr = Expression::bin(BinOp::Plus, left, right);

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::Plus, _, _) => {}
            _ => panic!("Expected Bin(Plus)"),
        }
    }

    #[test]
    fn test_not_simplifies_equality_negation() {
        let expr = Expression::not(Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("x")),
            Expression::null(),
        ));

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::NotEqEq, _, _) => {}
            other => panic!("Expected !== after negating ===, got {other:?}"),
        }
    }

    #[test]
    fn test_not_pushes_negation_through_and() {
        let left = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("x")),
            Expression::number(Number::int(1)),
        );
        let right = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("y")),
            Expression::number(Number::int(2)),
        );
        let expr = Expression::not(Expression::bin(BinOp::And, left, right));

        match &expr.desc {
            ExpressionDesc::Bin(BinOp::Or, left, right) => {
                assert!(matches!(left.desc, ExpressionDesc::Bin(BinOp::NotEqEq, _, _)));
                assert!(matches!(right.desc, ExpressionDesc::Bin(BinOp::NotEqEq, _, _)));
            }
            other => panic!("Expected De Morgan rewrite after negating &&, got {other:?}"),
        }
    }

    #[test]
    fn test_statement_creation() {
        let stmt = Statement::break_();
        match stmt.desc {
            StatementDesc::Break => {}
            _ => panic!("Expected Break"),
        }
    }

    #[test]
    fn test_if_statement() {
        let cond = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(Ident::create_local("x")),
            Expression::number(Number::int(1)),
        );
        let then_ = vec![Statement::exp(Expression::number(Number::int(10)))];
        let else_ = vec![Statement::return_(Expression::number(Number::int(20)))];
        let stmt = Statement::if_(cond, then_, else_);

        match &stmt.desc {
            StatementDesc::Block(block) => {
                let [guard, fallthrough] = block.as_slice() else {
                    panic!("Expected a guard if and a fallthrough statement");
                };
                match &guard.desc {
                    StatementDesc::If(guard_cond, then_block, else_block) => {
                        match &guard_cond.desc {
                            ExpressionDesc::Bin(BinOp::NotEqEq, _, _) => {}
                            _ => panic!("Expected a negated equality guard"),
                        }
                        assert!(matches!(then_block.as_slice(), [Statement { desc: StatementDesc::Return(_), .. }]));
                        assert!(else_block.is_empty());
                    }
                    _ => panic!("Expected guard if"),
                }
                assert!(matches!(fallthrough.desc, StatementDesc::Exp(_)));
            }
            _ => panic!("Expected simplified guard block"),
        }
    }

    #[test]
    fn test_if_statement_merges_two_returns_into_a_conditional_return() {
        let stmt = Statement::if_(
            Expression::var(Ident::create_local("cond")),
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![Statement::return_(Expression::number(Number::int(2)))],
        );

        match &stmt.desc {
            StatementDesc::Return(expr) => match &expr.desc {
                ExpressionDesc::Cond(_, consequent, alternate) => {
                    assert!(matches!(consequent.desc, ExpressionDesc::Number(_)));
                    assert!(matches!(alternate.desc, ExpressionDesc::Number(_)));
                }
                _ => panic!("Expected a conditional return expression"),
            },
            _ => panic!("Expected a single return statement"),
        }
    }

    #[test]
    fn test_if_statement_merges_matching_assignments_into_a_conditional_assignment() {
        let target = Ident::create_local("result");
        let stmt = Statement::if_(
            Expression::var(Ident::create_local("cond")),
            vec![Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(target.clone()),
                Expression::number(Number::int(1)),
            ))],
            vec![Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(target.clone()),
                Expression::number(Number::int(2)),
            ))],
        );

        match &stmt.desc {
            StatementDesc::Exp(expr) => match &expr.desc {
                ExpressionDesc::Bin(BinOp::Eq, lhs, rhs) => {
                    assert!(matches!(lhs.desc, ExpressionDesc::Var(_)));
                    assert!(matches!(rhs.desc, ExpressionDesc::Cond(_, _, _)));
                }
                _ => panic!("Expected a merged assignment"),
            },
            _ => panic!("Expected a single assignment expression"),
        }
    }

    #[test]
    fn test_program_creation() {
        let stmt = Statement::return_(Expression::undefined(true));
        let program = Program::new(vec![stmt], vec![]);

        assert_eq!(program.block.len(), 1);
        assert!(program.exports.is_empty());
    }
}
