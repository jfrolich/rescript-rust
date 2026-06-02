//! JavaScript IR Printer - Generates JavaScript source code from JS IR.
//!
//! This module provides functionality to convert the JavaScript IR
//! into formatted JavaScript source code.

use super::op::{BinOp, Kind, Number, PropertyName, UsedStats};
use super::{
    Block, CallArity, CallInfo, CallKind, CaseClause, Delim, Expression, ExpressionDesc,
    ForDirection, JsRawInfo, ModulePathResolver, Statement, StatementDesc, StringClause, VIdent,
    VariableDeclaration, ocaml_eq_block, ocaml_eq_expression,
};
use crate::binary_ast::ppx::{
    JsExpClassification, JsStmtClassification, classify_js_exp, classify_js_stmt,
};
use crate::ident::Ident;
use crate::lambda::SwitchCaseTag;
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

#[derive(Clone, Default)]
struct NameScope {
    ident_names: HashMap<Ident, String>,
    next_suffix: HashMap<String, usize>,
}

enum JsxChildren<'a> {
    None,
    EmptyFragment,
    Slice(&'a [Expression]),
    Single(&'a Expression),
}

struct FunctionPrintContext<'a> {
    is_method: bool,
    params: &'a [Ident],
    body: &'a Block,
    return_unit: bool,
    async_: bool,
    directive: Option<&'a str>,
    function_ident: Option<&'a Ident>,
}

/// JavaScript printer state
pub struct JsPrinter {
    /// Output buffer
    output: String,
    /// Current indentation level
    indent: usize,
    /// Matches OCaml's Ext_pp.last_new_line state.
    last_new_line: bool,
    /// Indentation string (2 spaces)
    indent_str: &'static str,
    /// Assigned printable names for identifiers in the active lexical scopes.
    name_scopes: Vec<NameScope>,
    /// Module-path resolver used for printing import declarations.
    pub(super) module_path_resolver: Option<ModulePathResolver>,
    /// Matches OCaml's `!Js_config.debug` toggle in the dumper.
    debug: bool,
    /// Matches OCaml's `!Js_config.jsx_preserve` guard in the dumper.
    jsx_preserve: bool,
    /// Suppresses extra multiline call-argument grouping while printing the target
    /// of a dot-style member access like `foo(...).bar`.
    suppress_member_target_call_arg_group_indent: usize,
}

impl Default for JsPrinter {
    fn default() -> Self {
        Self::new()
    }
}

impl JsPrinter {
    /// Create a new printer
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
            last_new_line: false,
            indent_str: "  ",
            name_scopes: vec![NameScope::default()],
            module_path_resolver: None,
            debug: false,
            jsx_preserve: false,
            suppress_member_target_call_arg_group_indent: 0,
        }
    }

    /// Create a new printer with a preallocated output buffer.
    pub fn with_capacity(capacity: usize) -> Self {
        let mut printer = Self::new();
        printer.output = String::with_capacity(capacity);
        printer
    }

    /// Create a new printer with module import resolution context.
    pub fn with_module_path_resolver(module_path_resolver: Option<&ModulePathResolver>) -> Self {
        Self::with_module_path_resolver_and_options(module_path_resolver, false, false)
    }

    /// Create a new printer with module import resolution context and debug mode.
    pub fn with_module_path_resolver_and_debug(
        module_path_resolver: Option<&ModulePathResolver>,
        debug: bool,
    ) -> Self {
        Self::with_module_path_resolver_and_options(module_path_resolver, debug, false)
    }

    /// Create a new printer with module import resolution context and dumper options.
    pub fn with_module_path_resolver_and_options(
        module_path_resolver: Option<&ModulePathResolver>,
        debug: bool,
        jsx_preserve: bool,
    ) -> Self {
        let mut printer = Self::with_capacity(0);
        printer.module_path_resolver = module_path_resolver.cloned();
        printer.debug = debug;
        printer.jsx_preserve = jsx_preserve;
        printer
    }

    pub(crate) fn with_module_path_resolver_options_and_capacity(
        module_path_resolver: Option<&ModulePathResolver>,
        debug: bool,
        jsx_preserve: bool,
        capacity: usize,
    ) -> Self {
        let mut printer = Self::with_capacity(capacity);
        printer.module_path_resolver = module_path_resolver.cloned();
        printer.debug = debug;
        printer.jsx_preserve = jsx_preserve;
        printer
    }

    /// Get the generated JavaScript code
    pub fn into_output(self) -> String {
        self.output
    }

    /// Get a reference to the output
    pub fn output(&self) -> &str {
        &self.output
    }

    /// Write a string
    pub(super) fn write(&mut self, s: &str) {
        self.output.push_str(s);
        self.last_new_line = false;
    }

    fn expression_string_in_current_scope(&self, expr: &Expression, level: u8) -> String {
        let mut printer = Self {
            output: String::new(),
            indent: 0,
            last_new_line: false,
            indent_str: self.indent_str,
            name_scopes: self.name_scopes.clone(),
            module_path_resolver: self.module_path_resolver.clone(),
            debug: self.debug,
            jsx_preserve: self.jsx_preserve,
            suppress_member_target_call_arg_group_indent: self
                .suppress_member_target_call_arg_group_indent,
        };
        printer.print_expression(expr, level);
        printer.output
    }

    fn nullish_or_target<'a>(
        &self,
        left: &'a Expression,
        right: &'a Expression,
    ) -> Option<&'a Expression> {
        fn strict_nullish_target(expr: &Expression) -> Option<(&Expression, bool)> {
            let ExpressionDesc::Bin(BinOp::EqEqEq, tested, literal) = &expr.desc else {
                return None;
            };
            match literal.as_ref().desc {
                ExpressionDesc::Null => Some((tested.as_ref(), true)),
                ExpressionDesc::Undefined { .. } => Some((tested.as_ref(), false)),
                _ => None,
            }
        }

        let (left_target, left_is_null) = strict_nullish_target(left)?;
        let (right_target, right_is_null) = strict_nullish_target(right)?;
        if left_is_null == right_is_null {
            return None;
        }

        let left_rendered = self.expression_string_in_current_scope(left_target, 0);
        let right_rendered = self.expression_string_in_current_scope(right_target, 0);
        if left_rendered == right_rendered {
            Some(left_target)
        } else {
            None
        }
    }

    /// Write a character
    pub(super) fn write_char(&mut self, c: char) {
        self.output.push(c);
        self.last_new_line = false;
    }

    /// Write a newline with current indentation
    pub(super) fn newline(&mut self) {
        if !self.last_new_line {
            self.output.push('\n');
            for _ in 0..self.indent {
                self.output.push_str(self.indent_str);
            }
            self.last_new_line = true;
        }
    }

    /// Match OCaml's Ext_pp.at_least_two_lines.
    pub(super) fn at_least_two_lines(&mut self) {
        if !self.last_new_line {
            self.output.push('\n');
        }
        self.output.push('\n');
        for _ in 0..self.indent {
            self.output.push_str(self.indent_str);
        }
        self.last_new_line = true;
    }

    /// Match OCaml's Ext_pp.force_newline.
    fn force_newline(&mut self) {
        self.output.push('\n');
        for _ in 0..self.indent {
            self.output.push_str(self.indent_str);
        }
        self.last_new_line = true;
    }

    /// Write a space
    fn space(&mut self) {
        self.output.push(' ');
    }

    /// Write a semicolon
    pub(super) fn semi(&mut self) {
        self.output.push(';');
        self.last_new_line = false;
    }

    /// Increase indentation
    pub(super) fn indent(&mut self) {
        self.indent += 1;
    }

    /// Decrease indentation
    pub(super) fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    fn with_indent<F>(&mut self, extra: usize, action: F)
    where
        F: FnOnce(&mut Self),
    {
        self.indent += extra;
        action(self);
        self.indent = self.indent.saturating_sub(extra);
    }

    fn print_paren_vgroup<F>(&mut self, extra: usize, action: F)
    where
        F: FnOnce(&mut Self),
    {
        self.write_char('(');
        self.with_indent(extra, |this| {
            this.newline();
            action(this);
        });
        self.newline();
        self.write_char(')');
    }

    fn current_name_scope_mut(&mut self) -> &mut NameScope {
        self.name_scopes
            .last_mut()
            .expect("printer must always have a name scope")
    }

    fn lookup_visible_name(&self, id: &Ident) -> Option<String> {
        self.name_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.ident_names.get(id).cloned())
    }

    fn reserve_printed_name(scope: &mut NameScope, printed: &str) {
        let (base, next_suffix) = printed_name_base_and_next_suffix(printed);
        let next = scope.next_suffix.entry(base).or_insert(0);
        *next = (*next).max(next_suffix);
    }

    fn visible_next_suffix_for_base(&self, base: &str) -> Option<usize> {
        self.name_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.next_suffix.get(base).copied())
    }

    fn assign_scoped_ident_name(&mut self, id: &Ident, base: String) -> String {
        let next = self
            .current_name_scope_mut()
            .next_suffix
            .entry(base.clone())
            .or_insert(0);
        let printed = if *next == 0 {
            base.clone()
        } else {
            format!("{base}${next}")
        };
        *next += 1;
        self.current_name_scope_mut()
            .ident_names
            .insert(id.clone(), printed.clone());
        printed
    }

    fn fresh_scoped_name(&mut self, base: String) -> String {
        let next = self
            .current_name_scope_mut()
            .next_suffix
            .entry(base.clone())
            .or_insert(0);
        let printed = if *next == 0 {
            base.clone()
        } else {
            format!("{base}${next}")
        };
        *next += 1;
        printed
    }

    /// Get a unique name for an identifier
    pub(super) fn ident_name(&mut self, id: &Ident) -> String {
        if let Some(name) = self.lookup_visible_name(id) {
            return name;
        }

        if id.stamp() == 0 {
            return id.name().to_string();
        }

        self.assign_scoped_ident_name(id, convert_ident_name(id.name()))
    }

    pub(super) fn module_ident_name(&mut self, id: &Ident) -> String {
        if let Some(name) = self.lookup_visible_name(id) {
            return name;
        }

        let base = convert_ident_name(id.name());
        self.assign_scoped_ident_name(id, base)
    }

    /// Print statements
    pub fn print_statements(&mut self, stmts: &[Statement], top_level: bool) {
        for (index, stmt) in stmts.iter().enumerate() {
            if index > 0 {
                if top_level {
                    self.at_least_two_lines();
                } else {
                    self.newline();
                }
            }
            if self.statement_prints_anything(stmt, top_level) {
                self.print_statement(stmt, top_level);
            }
        }
    }

    /// Print a statement
    pub fn print_statement(&mut self, stmt: &Statement, top_level: bool) {
        // Print comment if present
        if let Some(ref comment) = stmt.comment {
            self.write("/* ");
            self.write(comment);
            self.write(" */");
            self.newline();
        }

        self.print_statement_desc(&stmt.desc, top_level);
    }

    fn statement_prints_anything(&self, stmt: &Statement, top_level: bool) -> bool {
        stmt.comment.is_some() || self.statement_desc_prints_anything(&stmt.desc, top_level)
    }

    fn statement_desc_prints_anything(&self, desc: &StatementDesc, _top_level: bool) -> bool {
        match desc {
            StatementDesc::Block(stmts) => stmts
                .iter()
                .any(|stmt| self.statement_prints_anything(stmt, false)),
            StatementDesc::Variable(decl) => match decl.ident_info.used_stats {
                UsedStats::DeadPure => false,
                UsedStats::DeadNonPure => decl
                    .value
                    .as_ref()
                    .is_some_and(|value| !matches!(value.desc, ExpressionDesc::Var(_))),
                _ => true,
            },
            StatementDesc::Exp(expr) => expression_statement_prints_anything(expr),
            _ => true,
        }
    }

    /// Print a statement description
    fn print_statement_desc(&mut self, desc: &StatementDesc, top_level: bool) {
        match desc {
            StatementDesc::Block(stmts) => {
                if stmts.is_empty() {
                    return;
                }
                self.print_statements(stmts, false);
            }

            StatementDesc::Variable(decl) => {
                match decl.ident_info.used_stats {
                    UsedStats::DeadPure => return,
                    UsedStats::DeadNonPure => {
                        if let Some(value) = &decl.value {
                            self.print_expression_statement(value);
                        }
                        return;
                    }
                    _ => {}
                }

                if top_level {
                    if let Some(Expression {
                        desc:
                            ExpressionDesc::Fun {
                                is_method,
                                params,
                                body,
                                return_unit,
                                async_,
                                directive,
                                ..
                            },
                        ..
                    }) = &decl.value
                    {
                        self.print_function_declaration(
                            &decl.ident,
                            *is_method,
                            params,
                            body,
                            *return_unit,
                            *async_,
                            directive.as_deref(),
                        );
                        return;
                    }
                }

                self.print_variable_declaration(decl);
            }

            StatementDesc::Exp(expr) => {
                self.print_expression_statement(expr);
            }

            StatementDesc::If(cond, then_block, else_block) => {
                self.write("if ");
                self.write_char('(');
                self.with_indent(1, |this| this.print_expression(cond, 0));
                self.write(") ");
                self.print_brace_block(then_block);

                if !else_block_is_omitted_like_ocaml(else_block) {
                    self.write(" else ");
                    if let Some(nested_if) = single_else_if_stmt_like_ocaml(else_block) {
                        self.print_statement(nested_if, false);
                        return;
                    }
                    self.print_brace_block(else_block);
                }
            }

            StatementDesc::While(label, cond, body) => {
                if let Some(label) = label {
                    self.write(label);
                    self.write(": ");
                }
                self.write("while ");
                self.write_char('(');
                self.with_indent(1, |this| this.print_expression(cond, 0));
                self.write(") ");
                self.print_brace_block(body);
                self.semi();
            }

            StatementDesc::ForRange(label, init, end, id, direction, body) => {
                if let Some(label) = label {
                    self.write(label);
                    self.write(": ");
                }
                // OCaml's js_dump.ml:1415 threads its Ext_pp_scope cxt through
                // the for-body without calling sub_scope — sub_scope only runs
                // on function entry (js_dump.ml:369). Keeping the body in the
                // current scope lets inner `let v` bindings see the outer
                // next_suffix counters so stamp-distinct shadowing vars get
                // their `$N` rename (matches Ext_pp_scope.add_ident's
                // cardinal-based counter).
                let id_name = self.ident_name(id);
                let finish_binding = for_range_finish_needs_binding(end).then(|| {
                    self.fresh_scoped_name(format!("{}_finish", convert_ident_name(id.name())))
                });

                self.write("for ");
                self.write_char('(');

                match (init, finish_binding.as_deref()) {
                    (Some(init_expr), Some(finish_name)) => {
                        self.write("let ");
                        self.write(&id_name);
                        self.write(" = ");
                        self.print_expression(init_expr, 1);
                        self.write(", ");
                        self.write(finish_name);
                        self.write(" = ");
                        self.print_expression(end, 1);
                    }
                    (Some(init_expr), None) => {
                        self.write("let ");
                        self.write(&id_name);
                        self.write(" = ");
                        self.print_expression(init_expr, 1);
                    }
                    (None, Some(finish_name)) => {
                        self.write("let ");
                        self.write(finish_name);
                        self.write(" = ");
                        self.print_expression(end, 1);
                    }
                    (None, None) => {}
                }

                self.semi();
                self.space();

                self.write(&id_name);
                match direction {
                    ForDirection::Upto => self.write(" <= "),
                    ForDirection::Downto => self.write(" >= "),
                    ForDirection::Up => self.write(" < "),
                }
                if let Some(finish_name) = finish_binding.as_deref() {
                    self.write(finish_name);
                } else {
                    self.print_expression(end, 0);
                }
                self.semi();
                self.space();

                match direction {
                    ForDirection::Upto | ForDirection::Up => {
                        self.write("++");
                        self.write(&id_name);
                    }
                    ForDirection::Downto => {
                        self.write("--");
                        self.write(&id_name);
                    }
                }

                self.write(") ");
                self.print_brace_block(body);
            }

            StatementDesc::ForOf(label, id, iterable, body) => {
                if let Some(label) = label {
                    self.write(label);
                    self.write(": ");
                }
                self.write("for ");
                self.write_char('(');
                // OCaml uses `P.paren_group f 1` (js_dump.ml:1516) which adds
                // one indent level inside the parens so a multi-line iterable
                // (e.g. an inline array) continues at `base + 2` rather than
                // `base + 1`.
                let id_name = self.ident_name(id);
                self.with_indent(1, |this| {
                    this.write("let ");
                    this.write(&id_name);
                    this.write(" of ");
                    this.print_expression(iterable, 0);
                });
                self.write(") ");
                self.print_brace_block(body);
            }

            StatementDesc::ForAwaitOf(label, id, iterable, body) => {
                if let Some(label) = label {
                    self.write(label);
                    self.write(": ");
                }
                self.write("for await ");
                self.write_char('(');
                let id_name = self.ident_name(id);
                self.with_indent(1, |this| {
                    this.write("let ");
                    this.write(&id_name);
                    this.write(" of ");
                    this.print_expression(iterable, 0);
                });
                self.write(") ");
                self.print_brace_block(body);
            }

            StatementDesc::Continue(label) => {
                self.write("continue");
                if let Some(label) = label {
                    self.write(" ");
                    self.write(label);
                }
                self.semi();
            }

            StatementDesc::Break(label) => {
                self.write("break");
                if let Some(label) = label {
                    self.write(" ");
                    self.write(label);
                }
                self.semi();
            }

            StatementDesc::Return(expr) => {
                // Check for undefined return
                if matches!(expr.desc, ExpressionDesc::Undefined { .. }) {
                    self.write("return");
                    self.semi();
                    return;
                }

                self.write("return ");
                self.print_expression(expr, 0);
                self.semi();
            }

            StatementDesc::IntSwitch(expr, cases, default) => {
                self.write("switch ");
                self.write_char('(');
                self.print_expression(expr, 0);
                self.write(") {");
                self.indent();

                for (value, clause) in cases {
                    self.print_int_case(*value, clause);
                }

                if let Some(default_block) = default {
                    self.newline();
                    self.write("default:");
                    self.indent();
                    self.newline();
                    self.print_statements(default_block, false);
                    self.dedent();
                }

                self.dedent();
                self.newline();
                self.write_char('}');
            }

            StatementDesc::StringSwitch(expr, cases, default) => {
                self.write("switch ");
                self.write_char('(');
                self.print_expression(expr, 0);
                self.write(") {");
                self.indent();

                for clause in cases {
                    self.print_string_case(clause);
                }

                if let Some(default_block) = default {
                    self.newline();
                    self.write("default:");
                    self.indent();
                    self.newline();
                    self.print_statements(default_block, false);
                    self.dedent();
                }

                self.dedent();
                self.newline();
                self.write_char('}');
            }

            StatementDesc::Throw(expr) => {
                self.write("throw ");
                if !self.try_print_exception_block(expr, 0, true) {
                    self.print_expression(expr, 0);
                }
                self.semi();
            }

            StatementDesc::Try(body, catch, finally) => {
                self.write("try ");
                self.print_brace_block(body);

                if let Some((exn_id, catch_block)) = catch {
                    let exn_name = self.ident_name(exn_id);
                    self.write(" catch (");
                    self.write(&exn_name);
                    self.write(") ");
                    self.print_brace_block(catch_block);
                }

                if let Some(finally_block) = finally {
                    self.write(" finally ");
                    self.print_brace_block(finally_block);
                }
            }

            StatementDesc::Debugger => {
                self.write("debugger");
                self.semi();
            }
        }
    }

    fn print_expression_statement(&mut self, expr: &Expression) {
        // OCaml's js_dump suppresses dead pure bindings entirely and prints dead
        // impure bindings as plain expression statements.
        match classify_raw_js_expression_statement(expr) {
            RawJsExpressionStatement::Omit => return,
            RawJsExpressionStatement::Comment(comment) => {
                self.write(&comment);
                return;
            }
            RawJsExpressionStatement::Normal => {}
        }

        if matches!(expr.desc, ExpressionDesc::Var(_)) {
            return;
        }
        let needs_paren = self.expr_needs_paren(expr);
        if needs_paren {
            // OCaml js_dump.ml:1351-1353 wraps expression statements with
            // P.paren_group f 1, so multiline object/function bodies inherit
            // one extra indentation level while the surrounding parens print.
            self.with_indent(1, |this| {
                this.write_char('(');
                this.print_expression(expr, 0);
                this.write_char(')');
            });
        } else {
            self.print_expression(expr, 0);
        }
        self.semi();
    }

    /// Print a brace-enclosed block
    fn print_brace_block(&mut self, stmts: &Block) {
        self.write_char('{');
        self.indent();
        self.newline();
        self.print_statements(stmts, false);
        self.dedent();
        self.force_newline();
        self.write_char('}');
    }

    /// Print a variable declaration
    fn print_variable_declaration(&mut self, decl: &VariableDeclaration) {
        // Eta-reduce `let f = function(x, y) { return g(x, y); }` to `let f = g;`
        // at print time, matching OCaml's pp_function
        // (compiler/core/js_dump.ml:299-344) for the `Name_non_top` fn_state.
        if let Some(Expression {
            desc:
                ExpressionDesc::Fun {
                    is_method,
                    params,
                    body,
                    ..
                },
            ..
        }) = &decl.value
        {
            if let Some(target) = eta_reduce_function_body(*is_method, params, body) {
                self.write("let ");
                let var_name = self.ident_name(&decl.ident);
                self.write(&var_name);
                self.write(" = ");
                self.with_function_ident_scope(params, body, Some(&decl.ident), |this| {
                    this.print_vident(target);
                });
                self.semi();
                return;
            }
        }

        if let Some(Expression {
            desc: ExpressionDesc::Fun { params, body, .. },
            ..
        }) = &decl.value
        {
            // OCaml reserves the unbounded function environment plus the
            // Name_non_top binding before printing it; see
            // compiler/core/js_dump.ml:337-345 and 411-414.
            let reserved_idents = function_reserved_idents(params, body, Some(&decl.ident));
            self.reserve_idents_in_current_scope(&reserved_idents);
        }

        let var_name = self.ident_name(&decl.ident);
        self.write("let ");
        self.write(&var_name);

        if let Some(value) = &decl.value {
            if !is_undefined_literal(value) {
                self.write(" = ");
                if let ExpressionDesc::Fun {
                    is_method,
                    params,
                    body,
                    return_unit,
                    async_,
                    directive,
                    ..
                } = &value.desc
                {
                    // OCaml reference: compiler/core/js_dump.ml:337-360 builds
                    // `set_env` including `Name_non_top id`, then
                    // compiler/core/js_dump.ml:411-414 prints the function in
                    // `inner_cxt`.
                    // That makes the function's own binding name reserved inside
                    // the body, so body-local bindings with the same source name
                    // get `$N` suffixes.
                    self.print_function_expression(FunctionPrintContext {
                        is_method: *is_method,
                        params,
                        body,
                        return_unit: *return_unit,
                        async_: *async_,
                        directive: directive.as_deref(),
                        function_ident: Some(&decl.ident),
                    });
                } else {
                    self.print_expression(value, 1);
                }
            }
        }

        self.semi();
    }

    fn with_function_ident_scope<T>(
        &mut self,
        params: &[Ident],
        body: &Block,
        function_ident: Option<&Ident>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let reserved_idents = function_reserved_idents(params, body, function_ident);

        let mut scope = NameScope::default();
        for ident in reserved_idents {
            let printed = self.ident_name(&ident);
            let (base, next_suffix) = printed_name_base_and_next_suffix(&printed);
            // OCaml's Ext_pp_scope.sub_scope copies the whole stamp map for a
            // captured mangled name, not just the one captured identifier
            // (compiler/ext/ext_pp_scope.ml:109-117). That means capturing
            // outer `match` also reserves an already-visible sibling
            // `match$1`, so body-local `match` starts at `match$2`.
            let visible_next = self
                .visible_next_suffix_for_base(&base)
                .unwrap_or(next_suffix);
            scope
                .next_suffix
                .insert(base, visible_next.max(next_suffix));
        }

        self.name_scopes.push(scope);
        let out = f(self);
        self.name_scopes.pop();
        out
    }

    fn print_function_expression(&mut self, context: FunctionPrintContext<'_>) {
        let FunctionPrintContext {
            is_method,
            params,
            body,
            return_unit,
            async_,
            directive,
            function_ident,
        } = context;

        // compiler/core/js_dump.ml:342-344 - when a function expression's body is
        // `[ Return (Call (Var v, args, _)) ]` with each
        // `args[i] == Var(params[i])` and the callee is ML/runtime,
        // collapse the expression to the underlying `v`. This mirrors
        // OCaml's `Is_return | No_name _` arm of pp_function that emits
        // `optimize len ~p cxt f v` -> `vident` for the clean
        // `arity = Full, call_info = Call_ml | Call_builtin_runtime` case.
        if let Some(target) = eta_reduce_function_body(is_method, params, body) {
            self.with_function_ident_scope(params, body, function_ident, |this| {
                this.print_vident(target);
            });
            return;
        }

        let use_arrow = !is_method;
        self.with_function_ident_scope(params, body, function_ident, |this| {
            let (this_binding, param_names) =
                this.method_params_and_binding(is_method, params, body);

            // Async prefix
            if async_ {
                this.write("async ");
            }

            // Function keyword or arrow
            if !use_arrow {
                this.write("function");
                this.write(" ");
            }

            // Parameters
            if param_names.len() == 1 && use_arrow {
                this.write(&param_names[0]);
            } else {
                this.write_char('(');
                for (i, name) in param_names.iter().enumerate() {
                    if i > 0 {
                        this.write(", ");
                    }
                    this.write(name);
                }
                this.write_char(')');
            }

            if use_arrow {
                this.write(" =>");
            }

            // Body
            if use_arrow
                && directive.is_none()
                && body.as_slice().len() == 1
                && matches!(
                    body[0].desc,
                    StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Undefined { .. },
                        ..
                    })
                )
            {
                this.write(" {}");
                return;
            }

            if use_arrow
                && directive.is_none()
                && let Some(expr) = single_arrow_function_expr(body)
            {
                this.write(" ");
                let needs_paren = this.arrow_expr_needs_paren(expr);
                if needs_paren {
                    this.write_char('(');
                }
                this.print_expression(expr, 0);
                if needs_paren {
                    this.write_char(')');
                }
                return;
            }

            this.print_function_body_block(body, return_unit, directive, this_binding.as_ref());
        });
    }

    pub(super) fn reserve_idents_in_current_scope(&mut self, idents: &[Ident]) {
        for ident in idents {
            if ident.stamp() == 0 {
                // OCaml `Ext_pp_scope.merge` reserves the converted printed
                // name for every id in a function environment, including
                // stamp-0 JS globals; see compiler/ext/ext_pp_scope.ml:98-100.
                let base = convert_ident_name(ident.name());
                Self::reserve_printed_name(self.current_name_scope_mut(), &base);
            } else {
                let _ = self.ident_name(ident);
            }
        }
    }

    fn print_function_declaration(
        &mut self,
        ident: &Ident,
        is_method: bool,
        params: &[Ident],
        body: &Block,
        return_unit: bool,
        async_: bool,
        directive: Option<&str>,
    ) {
        // Eta-reduce `function f(x, y) { return g(x, y); }` to `let f = g;`.
        // OCaml's js_dump.ml:299-344 does this at print time when the body is
        // a single `return Call(Var v, ls, _)` whose argument list matches the
        // parameter list positionally and v does not appear in the params (to
        // avoid turning `function x { return x(x); }` into `let x = x;`).
        if let Some(target) = eta_reduce_function_body(is_method, params, body) {
            self.write("let ");
            let fn_name = self.ident_name(ident);
            self.write(&fn_name);
            self.write(" = ");
            self.with_function_ident_scope(params, body, Some(ident), |this| {
                this.print_vident(target);
            });
            self.semi();
            return;
        }
        // OCaml reserves the unbounded function environment plus the Name_top
        // binding before printing the function id; see
        // compiler/core/js_dump.ml:337-345 and 416-419.
        let reserved_idents = function_reserved_idents(params, body, Some(ident));
        self.reserve_idents_in_current_scope(&reserved_idents);
        if async_ {
            self.write("async ");
        }
        self.write("function ");
        let fn_name = self.ident_name(ident);
        self.write(&fn_name);
        self.with_function_ident_scope(params, body, Some(ident), |this| {
            let (this_binding, rendered_params) =
                this.method_params_and_binding(is_method, params, body);
            this.write_char('(');
            for (i, param_name) in rendered_params.iter().enumerate() {
                if i > 0 {
                    this.write(", ");
                }
                this.write(param_name);
            }
            this.write_char(')');
            this.print_function_body_block(body, return_unit, directive, this_binding.as_ref());
        });
    }

    fn method_params_and_binding(
        &mut self,
        is_method: bool,
        params: &[Ident],
        body: &Block,
    ) -> (Option<String>, Vec<String>) {
        if !is_method {
            let rendered_params = params.iter().map(|param| self.ident_name(param)).collect();
            return (None, rendered_params);
        }

        let (this_param, args) = params
            .split_first()
            .expect("method functions must carry an explicit `this` parameter");
        let free = free_variables_of_block_with_defined(body, std::iter::empty());
        let this_binding = free
            .contains(this_param)
            .then(|| self.ident_name(this_param));
        let rendered_params = args.iter().map(|param| self.ident_name(param)).collect();
        (this_binding, rendered_params)
    }

    fn print_function_body_block(
        &mut self,
        body: &Block,
        return_unit: bool,
        directive: Option<&str>,
        this_binding: Option<&String>,
    ) {
        let body_prints_any = function_body_prints_any(body);
        self.write(" {");
        if this_binding.is_none() && directive.is_none() && !body_prints_any {
            self.indent();
            self.output.push('\n');
            for _ in 0..self.indent {
                self.output.push_str(self.indent_str);
            }
            self.output.push('\n');
            self.last_new_line = true;
            self.dedent();
            self.write_char('}');
            return;
        }
        if this_binding.is_some() || !body.is_empty() || directive.is_some() {
            self.indent();
            if let Some(this_binding) = this_binding {
                self.newline();
                self.write("let ");
                self.write(this_binding);
                self.write(" = this ");
                self.semi();
            }
            if directive.is_some() || body_prints_any {
                self.print_function_directive(directive, body_prints_any);
                self.print_function_body(body, return_unit);
            }
            self.dedent();
            self.newline();
        }
        self.write_char('}');
    }

    fn print_function_directive(&mut self, directive: Option<&str>, body_follows: bool) {
        if let Some(directive) = directive {
            self.newline();
            self.write(directive);
            self.write_char(';');
            if body_follows {
                self.newline();
            }
        } else if body_follows {
            self.newline();
        }
    }

    /// Print an integer case
    fn print_int_case(&mut self, value: i32, clause: &CaseClause) {
        self.newline();
        self.write("case ");
        write!(self.output, "{}", value).unwrap();
        self.last_new_line = false;
        self.write(" :");

        if !clause.body.is_empty() || clause.should_break {
            self.indent();
            self.newline();
            if !clause.body.is_empty() {
                self.print_statements(&clause.body, false);
            }
            if clause.should_break {
                if !clause.body.is_empty() {
                    self.newline();
                }
                self.write("break");
                self.semi();
            }
            self.dedent();
        }
    }

    fn print_switch_case_tag(&mut self, tag: &SwitchCaseTag) {
        match tag {
            SwitchCaseTag::String(value) => self.print_string_with_delim(value, Delim::StarJ),
            SwitchCaseTag::Int(value) => {
                write!(self.output, "{value}").unwrap();
                self.last_new_line = false;
            }
            SwitchCaseTag::Float(value) => self.write(value),
            SwitchCaseTag::BigInt(value) => {
                self.write(value);
                self.write("n");
            }
            SwitchCaseTag::Bool(value) => self.write(if *value { "true" } else { "false" }),
            SwitchCaseTag::Null => self.write("null"),
            SwitchCaseTag::Undefined => self.write("undefined"),
        }
    }

    /// Print a literal switch case.
    fn print_string_case(&mut self, clause: &StringClause) {
        self.newline();
        self.write("case ");
        self.print_switch_case_tag(&clause.tag_type);
        self.write(" :");

        if !clause.clause.body.is_empty() || clause.clause.should_break {
            self.indent();
            self.newline();
            if !clause.clause.body.is_empty() {
                self.print_statements(&clause.clause.body, false);
            }
            if clause.clause.should_break {
                if !clause.clause.body.is_empty() {
                    self.newline();
                }
                self.write("break");
                self.semi();
            }
            self.dedent();
        }
    }

    /// Check if an expression needs parentheses when used as a statement
    fn expr_needs_paren(&self, expr: &Expression) -> bool {
        match &expr.desc {
            ExpressionDesc::Call(func, _, _) => matches!(func.desc, ExpressionDesc::RawJsCode(_)),
            ExpressionDesc::RawJsCode(info) => !info.is_stmt,
            ExpressionDesc::Fun { .. } | ExpressionDesc::Object(_, _) => true,
            _ => false,
        }
    }

    fn arrow_expr_needs_paren(&self, expr: &Expression) -> bool {
        match &expr.desc {
            ExpressionDesc::Fun { .. } | ExpressionDesc::Object(_, _) => true,
            ExpressionDesc::RawJsCode(info) => !info.is_stmt,
            ExpressionDesc::CamlBlock(_, _, _, tag_info) => matches!(
                tag_info,
                crate::lambda::TagInfo::Record { .. }
                    | crate::lambda::TagInfo::Module(_)
                    | crate::lambda::TagInfo::PolyVar(_)
                    | crate::lambda::TagInfo::Extension
                    | crate::lambda::TagInfo::RecordExt { .. }
                    | crate::lambda::TagInfo::RecordInlined { .. }
                    | crate::lambda::TagInfo::Constructor { .. }
            ),
            ExpressionDesc::OptionalBlock(inner, true) => self.arrow_expr_needs_paren(inner),
            _ => false,
        }
    }

    fn transformed_jsx_call_name<'a>(
        &self,
        func: &'a Expression,
        info: &CallInfo,
    ) -> Option<&'a str> {
        if !info.call_transformed_jsx {
            return None;
        }

        let name = match &func.desc {
            ExpressionDesc::Var(VIdent::Id(id)) => Some(id.name()),
            ExpressionDesc::Var(VIdent::Qualified(_, Some(name))) => Some(name.as_str()),
            _ => None,
        }?;

        matches!(name, "jsx" | "jsxs").then_some(name)
    }

    fn is_jsx_fragment_tag(&self, tag: &Expression) -> bool {
        matches!(
            &tag.desc,
            ExpressionDesc::Var(VIdent::Qualified(module, Some(name)))
                if name == "Fragment"
                    && matches!(
                        &module.kind,
                        Kind::External { name, .. } if name == "react/jsx-runtime"
                    )
        )
    }

    fn collect_jsx_fields_from_object<'a>(
        &self,
        props: &'a [(PropertyName, Expression)],
    ) -> Option<Vec<(&'a str, &'a Expression)>> {
        let mut fields = Vec::with_capacity(props.len());
        for (name, value) in props {
            let PropertyName::Lit(name) = name else {
                return None;
            };
            fields.push((name.as_str(), value));
        }
        Some(fields)
    }

    fn collect_jsx_fields_from_record_block<'a>(
        &self,
        elements: &'a [Expression],
        fields: &'a [(String, bool)],
    ) -> Option<Vec<(&'a str, &'a Expression)>> {
        if elements.len() != fields.len() {
            return None;
        }

        let mut collected = Vec::with_capacity(fields.len());
        for ((name, optional), value) in fields.iter().zip(elements.iter()) {
            if *optional && is_undefined_literal(value) {
                continue;
            }
            collected.push((name.as_str(), value));
        }
        Some(collected)
    }

    fn collect_jsx_spread_assignments<'a>(
        &self,
        props: &'a Expression,
    ) -> Option<(Vec<(&'a str, &'a Expression)>, &'a Expression)> {
        fn visit<'a>(
            expr: &'a Expression,
            acc: &mut Vec<(&'a str, &'a Expression)>,
        ) -> Option<&'a Expression> {
            match &expr.desc {
                ExpressionDesc::Seq(first, rest) => match &first.desc {
                    ExpressionDesc::Bin(BinOp::Eq, target, value) => match &target.as_ref().desc {
                        ExpressionDesc::StaticIndex(_, name, _) => {
                            acc.push((name.as_str(), value.as_ref()));
                            visit(rest, acc)
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => Some(expr),
            }
        }

        let mut fields = Vec::new();
        let spread = visit(props, &mut fields)?;
        Some((fields, spread))
    }

    fn collect_transformed_jsx_props<'a>(
        &self,
        props: &'a Expression,
    ) -> Option<(Vec<(&'a str, &'a Expression)>, Option<&'a Expression>)> {
        match &props.desc {
            ExpressionDesc::Object(dup, props) => Some((
                self.collect_jsx_fields_from_object(props)?,
                dup.as_ref().map(|dup| dup.as_ref()),
            )),
            ExpressionDesc::CamlBlock(
                elements,
                _,
                _,
                crate::lambda::TagInfo::Record { fields, .. },
            ) => Some((
                self.collect_jsx_fields_from_record_block(elements, fields)?,
                None,
            )),
            ExpressionDesc::Seq(_, _) => {
                let (fields, spread_props) = self.collect_jsx_spread_assignments(props)?;
                Some((fields, Some(spread_props)))
            }
            ExpressionDesc::Var(_) => Some((Vec::new(), Some(props))),
            _ => None,
        }
    }

    fn jsx_children<'a>(
        &self,
        fn_name: &str,
        fields: &[(&'a str, &'a Expression)],
        is_fragment: bool,
    ) -> JsxChildren<'a> {
        for (name, expr) in fields {
            if *name != "children" {
                continue;
            }

            return if fn_name == "jsxs" {
                match &expr.desc {
                    ExpressionDesc::Array(children, _) => JsxChildren::Slice(children),
                    ExpressionDesc::OptionalBlock(inner, _) => match &inner.as_ref().desc {
                        ExpressionDesc::Array(children, _) => JsxChildren::Slice(children),
                        _ => JsxChildren::Single(expr),
                    },
                    _ => JsxChildren::Single(expr),
                }
            } else {
                JsxChildren::Single(expr)
            };
        }

        if is_fragment {
            JsxChildren::EmptyFragment
        } else {
            JsxChildren::None
        }
    }

    fn print_transformed_jsx_tag(&mut self, tag: &Expression, level: u8, is_fragment: bool) {
        match &tag.desc {
            ExpressionDesc::Str { txt, .. } => self.write(txt),
            _ if is_fragment => {}
            _ => self.print_expression(tag, level),
        }
    }

    fn print_transformed_jsx_key_prop(&mut self, key: &Expression) {
        self.write("key={");
        self.print_expression(key, 0);
        self.write("} ");
    }

    fn print_transformed_jsx_spread_prop(&mut self, spread: &Expression) {
        self.write("{...");
        self.print_expression(spread, 0);
        self.write("} ");
    }

    fn print_transformed_jsx_named_prop(&mut self, name: &str, value: &Expression) {
        self.write(unwrap_uppercase_exotic(name));
        self.write("={");
        self.print_expression(value, 0);
        self.write("}");
    }

    fn print_transformed_jsx_child(&mut self, child: &Expression) {
        let child_is_jsx = matches!(
            &child.desc,
            ExpressionDesc::Call(
                _,
                _,
                CallInfo {
                    call_transformed_jsx: true,
                    ..
                }
            )
        );
        if !child_is_jsx {
            self.write("{");
        }
        self.print_expression(child, 0);
        if !child_is_jsx {
            self.write("}");
        }
    }

    fn print_transformed_jsx(
        &mut self,
        level: u8,
        fn_name: &str,
        tag: &Expression,
        fields: &[(&str, &Expression)],
        spread_props: Option<&Expression>,
        key: Option<&Expression>,
    ) {
        let is_fragment = self.is_jsx_fragment_tag(tag);
        let children = self.jsx_children(fn_name, fields, is_fragment);
        let named_prop_count = fields
            .iter()
            .filter(|(name, _)| *name != "children")
            .count();
        let has_named_props = named_prop_count != 0;
        let printable_prop_count =
            usize::from(key.is_some()) + usize::from(spread_props.is_some()) + named_prop_count;

        if level > 15 {
            self.write_char('(');
        }

        self.write("<");
        self.print_transformed_jsx_tag(tag, level, is_fragment);

        if printable_prop_count == 0 {
            if matches!(children, JsxChildren::None) {
                self.write(" ");
            }
        } else {
            self.indent();
            self.newline();

            let mut remaining = printable_prop_count;
            if let Some(key) = key {
                self.print_transformed_jsx_key_prop(key);
                remaining -= 1;
                if remaining > 0 {
                    self.newline();
                }
            }
            if let Some(spread_props) = spread_props {
                self.print_transformed_jsx_spread_prop(spread_props);
                remaining -= 1;
                if remaining > 0 {
                    self.newline();
                }
            }
            let mut printed_named_props = 0;
            for (name, value) in fields.iter().filter(|(name, _)| *name != "children") {
                self.print_transformed_jsx_named_prop(name, value);
                printed_named_props += 1;
                if printed_named_props < named_prop_count {
                    self.newline();
                }
            }

            self.dedent();
        }

        match children {
            JsxChildren::None => {
                if has_named_props {
                    self.newline();
                }
                self.write("/>");
            }
            JsxChildren::EmptyFragment => {
                self.write("></>");
            }
            JsxChildren::Slice(children) if children.is_empty() && is_fragment => {
                self.write("></>");
            }
            JsxChildren::Slice(children) => {
                if has_named_props {
                    self.newline();
                }
                self.write(">");
                self.indent();
                for child in children {
                    self.newline();
                    self.print_transformed_jsx_child(child);
                }
                self.dedent();
                self.newline();
                self.write("</");
                self.print_transformed_jsx_tag(tag, level, is_fragment);
                self.write(">");
            }
            JsxChildren::Single(child) => {
                if has_named_props {
                    self.newline();
                }
                self.write(">");
                self.indent();
                self.newline();
                self.print_transformed_jsx_child(child);
                self.dedent();
                self.newline();
                self.write("</");
                self.print_transformed_jsx_tag(tag, level, is_fragment);
                self.write(">");
            }
        }

        if level > 15 {
            self.write_char(')');
        }
    }

    fn try_print_transformed_jsx_call(
        &mut self,
        func: &Expression,
        args: &[Expression],
        info: &CallInfo,
        level: u8,
    ) -> bool {
        if !self.jsx_preserve {
            return false;
        }

        let Some(fn_name) = self.transformed_jsx_call_name(func, info) else {
            return false;
        };

        let (tag, props, key) = match args {
            [tag, props] => (tag, props, None),
            [tag, props, key] => (tag, props, Some(key)),
            _ => return false,
        };
        let Some((fields, spread_props)) = self.collect_transformed_jsx_props(props) else {
            return false;
        };

        self.print_transformed_jsx(level, fn_name, tag, &fields, spread_props, key);
        true
    }

    /// Print an expression
    pub fn print_expression(&mut self, expr: &Expression, level: u8) {
        // Print comment if present
        if let Some(ref comment) = expr.comment {
            self.write("/* ");
            self.write(comment);
            self.write(" */");
        }

        self.print_expression_desc(&expr.desc, level);
    }

    /// Print an expression description
    fn print_expression_desc(&mut self, desc: &ExpressionDesc, level: u8) {
        match desc {
            ExpressionDesc::Null => {
                self.write("null");
            }

            ExpressionDesc::Undefined { .. } => {
                self.write("undefined");
            }

            ExpressionDesc::Var(vident) => {
                self.print_vident(vident);
            }

            ExpressionDesc::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }

            ExpressionDesc::Number(n) => {
                self.print_number(n, level);
            }

            ExpressionDesc::Str { delim, txt } => {
                self.print_string_with_delim(txt, *delim);
            }

            ExpressionDesc::Array(elements, _) => {
                self.print_array_literal(elements);
            }

            ExpressionDesc::Object(dup, props) => self.print_object_literal(
                level,
                dup.as_deref(),
                props.iter(),
                |this, (name, value)| {
                    this.print_property_name(name);
                    this.write(": ");
                    this.print_expression(value, 1);
                },
            ),

            ExpressionDesc::Seq(e1, e2) => {
                let needs_paren = level > 0;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_expression(e1, 0);
                self.write(", ");
                self.print_expression(e2, 0);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::Cond(cond, then_, else_) => {
                let print_cond = |this: &mut Self| {
                    this.print_expression(cond, 3);
                    this.write(" ? ");
                    this.with_indent(1, |this| this.print_expression(then_, 3));
                    this.write(" : ");
                    this.with_indent(1, |this| this.print_expression(else_, 3));
                };
                if level > 2 {
                    self.print_paren_vgroup(1, print_cond);
                } else {
                    print_cond(self);
                }
            }

            ExpressionDesc::Bin(op, left, right) => {
                if *op == BinOp::Minus {
                    match (&left.desc, &right.desc) {
                        (ExpressionDesc::Number(Number::Int { i: 0, .. }), _) => {
                            let needs_paren = level > 13;
                            if needs_paren {
                                self.write_char('(');
                            }
                            self.write_char('-');
                            self.print_expression(right, 13);
                            if needs_paren {
                                self.write_char(')');
                            }
                            return;
                        }
                        (ExpressionDesc::Number(Number::Float(float)), _) if float.f == "0." => {
                            let needs_paren = level > 13;
                            if needs_paren {
                                self.write_char('(');
                            }
                            self.write("- ");
                            self.print_expression(right, 13);
                            if needs_paren {
                                self.write_char(')');
                            }
                            return;
                        }
                        _ => {}
                    }
                }

                if *op == BinOp::Or {
                    if let Some(target) = self.nullish_or_target(left, right) {
                        let needs_paren = level > 0;
                        if needs_paren {
                            self.write_char('(');
                        }
                        self.print_expression(target, 1);
                        self.write(" == null");
                        if needs_paren {
                            self.write_char(')');
                        }
                        return;
                    }
                }

                let (out, lft, rght) = op_precedence(*op);
                // OCaml keeps shift operators parenthesized even in low-precedence
                // contexts to preserve the backend's conservative JS byte shape.
                let needs_paren = level > out || matches!(op, BinOp::Lsl | BinOp::Lsr | BinOp::Asr);
                if needs_paren {
                    self.write_char('(');
                }
                self.print_expression(left, lft);
                self.space();
                self.write(op.to_js_string());
                self.space();
                self.print_expression(right, rght);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::JsNot(e) => {
                let needs_paren = level > 13;
                if needs_paren {
                    self.write_char('(');
                }
                self.write_char('!');
                self.print_expression(e, 13);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::JsBnot(e) => {
                let needs_paren = level > 13;
                if needs_paren {
                    self.write_char('(');
                }
                self.write_char('~');
                self.print_expression(e, 13);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::Typeof(e) => {
                self.write("typeof ");
                if matches!(e.desc, ExpressionDesc::Fun { .. }) {
                    self.write_char('(');
                    self.print_expression(e, 13);
                    self.write_char(')');
                } else {
                    self.print_expression(e, 13);
                }
            }

            ExpressionDesc::In(prop, obj) => {
                let needs_paren = level > 12;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_expression(prop, 0);
                self.write(" in ");
                self.print_expression(obj, 0);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::Call(func, args, info) => {
                if self.try_print_transformed_jsx_call(func, args, info, level) {
                    return;
                }

                let needs_paren = level > 15;
                if needs_paren {
                    self.write_char('(');
                }

                // Wrap function expressions in parens
                if matches!(func.desc, ExpressionDesc::Fun { .. }) {
                    self.write_char('(');
                    self.print_expression(func, 15);
                    self.write_char(')');
                } else {
                    self.print_expression(func, 15);
                }

                self.write_char('(');
                let printed_args = match args.as_slice() {
                    // OCaml's js_dump.ml omits the synthetic unit argument so `f(())`
                    // prints as `f()`, while plain `undefined` stays explicit.
                    [
                        Expression {
                            desc: ExpressionDesc::Undefined { is_unit: true },
                            ..
                        },
                    ] => &[][..],
                    _ => args.as_slice(),
                };
                for (i, arg) in printed_args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_call_argument(arg, level);
                }
                self.write_char(')');

                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::FlatCall(func, args) => {
                self.print_expression(func, 15);
                self.write(".apply(null, ");
                self.print_expression(args, 1);
                self.write_char(')');
            }

            ExpressionDesc::New(ctor, args) => {
                let needs_paren = level > 15;
                if needs_paren {
                    self.write_char('(');
                }
                self.write("new ");
                let ctor_level = match &ctor.desc {
                    ExpressionDesc::StaticIndex(target, _, _)
                        if matches!(
                            target.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Var(VIdent::Qualified(module, None)),
                                ..
                            } if matches!(module.kind, Kind::External { .. })
                        ) =>
                    {
                        15
                    }
                    _ => 16,
                };
                self.print_expression(ctor, ctor_level);
                self.write_char('(');
                if let Some(args) = args {
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.print_call_argument(arg, level);
                    }
                }
                self.write_char(')');
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::ArrayIndex(arr, idx) => {
                // OCaml's `Array_index` printer (js_dump.ml:991-995) wraps the
                // inner expression in `P.group f 1` unconditionally — every
                // multi-line shape inside the target gets +1 indent. The
                // printer's `print_member_target_expression(_, true)` mirrors
                // that by raising the indent before delegating to the inner
                // expression.
                let needs_paren = level > 15;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_member_target_expression(arr, true);
                self.write_char('[');
                self.print_expression(idx, 0);
                self.write_char(']');
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::StringIndex(str_expr, idx) => {
                self.print_expression(str_expr, 15);
                self.write(".codePointAt(");
                self.print_expression(idx, 0);
                self.write_char(')');
            }

            ExpressionDesc::StaticIndex(obj, field, _) => {
                let needs_paren = level > 15;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_dot_member_target_expression(obj);
                self.print_property_access(field);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::Length(e, obj_type) => {
                let needs_paren = level > 15;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_dot_member_target_expression(e);
                self.write(".length");
                if needs_paren {
                    self.write_char(')');
                }
                let _ = obj_type; // Used for type-specific optimizations
            }

            ExpressionDesc::IsNullOrUndefined(e) => {
                let needs_paren = level > 0;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_expression(e, 1);
                self.write(" == null");
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::StringAppend(e1, e2) => {
                let (out, lft, rght) = op_precedence(BinOp::Plus);
                let needs_paren = level > out;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_expression(e1, lft);
                self.write(" + ");
                self.print_expression(e2, rght);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::Fun {
                is_method,
                params,
                body,
                return_unit,
                async_,
                directive,
                ..
            } => {
                self.print_function_expression(FunctionPrintContext {
                    is_method: *is_method,
                    params,
                    body,
                    return_unit: *return_unit,
                    async_: *async_,
                    directive: directive.as_deref(),
                    function_ident: None,
                });
            }

            ExpressionDesc::RawJsCode(info) => {
                self.print_raw_js(info);
            }

            ExpressionDesc::Await(e) => {
                let needs_paren = level > 13;
                if needs_paren {
                    self.write_char('(');
                }
                self.write("await ");
                self.print_expression(e, 13);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::Spread(e) => {
                let needs_paren = level > 13;
                if needs_paren {
                    self.write_char('(');
                }
                self.write("...");
                self.print_expression(e, 13);
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::TaggedTemplate(tag, strings, values) => {
                self.print_expression(tag, level);
                self.write_char('`');
                for (i, s) in strings.iter().enumerate() {
                    if let ExpressionDesc::Str { txt, .. } = &s.desc {
                        self.write_decoded_internal_string(txt);
                    }
                    if i < values.len() {
                        self.write("${");
                        self.print_expression(&values[i], 0);
                        self.write_char('}');
                    }
                }
                self.write_char('`');
            }

            ExpressionDesc::OptionalBlock(e, identity) => {
                if *identity {
                    self.print_expression(e, level);
                } else {
                    // Match OCaml's js_dump.ml by omitting the synthetic unit
                    // argument so `Some(())` prints as `Primitive_option.some()`.
                    self.write("Primitive_option.some(");
                    if !matches!(e.desc, ExpressionDesc::Undefined { is_unit: true }) {
                        self.print_expression(e, 1);
                    }
                    self.write_char(')');
                }
            }

            ExpressionDesc::CamlBlock(elements, _mutable, _tag, tag_info) => {
                use crate::lambda::TagInfo;

                if matches!(tag_info, TagInfo::Extension | TagInfo::RecordExt { .. }) {
                    self.print_exception_block_literal(level, elements, tag_info, false);
                    return;
                }

                // Check if this is a record with field names
                match tag_info {
                    TagInfo::Record { fields, .. } if fields.len() == elements.len() => {
                        if record_uses_array_syntax(fields) {
                            self.print_array_literal(elements);
                        } else {
                            self.print_object_literal(
                                level,
                                None,
                                elements.iter().zip(fields.iter()).filter_map(
                                    |(elem, (field_name, optional))| {
                                        if *optional && is_undefined_literal(elem) {
                                            None
                                        } else {
                                            Some((field_name.as_str(), elem))
                                        }
                                    },
                                ),
                                |this, (field_name, elem)| {
                                    this.print_literal_property_name(field_name);
                                    this.write(": ");
                                    this.print_expression(elem, 1);
                                },
                            );
                        }
                    }
                    TagInfo::RecordInlined {
                        name,
                        fields,
                        attrs,
                        ..
                    } if fields.len() == elements.len() => {
                        let untagged = tag_info_has_untagged(attrs);
                        let tag_name = tag_info_tag_name(attrs).unwrap_or("TAG");
                        let tag_value = tag_info_runtime_tag(attrs)
                            .unwrap_or_else(|| SwitchCaseTag::String(name.clone()));
                        self.print_object_literal(
                            level,
                            None,
                            (if untagged {
                                Vec::new()
                            } else {
                                vec![(None, None)]
                            })
                            .into_iter()
                            .chain(
                                elements.iter().zip(fields.iter()).filter_map(
                                    |(elem, (field_name, optional))| {
                                        if *optional && is_undefined_literal(elem) {
                                            None
                                        } else {
                                            Some((Some(field_name.as_str()), Some(elem)))
                                        }
                                    },
                                ),
                            ),
                            |this, prop| match prop {
                                (None, None) => {
                                    this.print_literal_property_name(tag_name);
                                    this.write(": ");
                                    this.print_switch_case_tag(&tag_value);
                                }
                                (Some(field_name), Some(elem)) => {
                                    this.print_literal_property_name(field_name);
                                    this.write(": ");
                                    this.print_expression(elem, 1);
                                }
                                _ => unreachable!("inline record literal properties stay aligned"),
                            },
                        );
                    }
                    TagInfo::Module(fields) if fields.len() == elements.len() => {
                        self.print_object_literal(
                            level,
                            None,
                            elements.iter().zip(fields.iter()),
                            |this, (elem, field_name)| {
                                let field_name = convert_ident_name(field_name);
                                this.print_literal_property_name(&field_name);
                                this.write(": ");
                                this.print_expression(elem, 1);
                            },
                        );
                    }
                    TagInfo::Constructor {
                        name,
                        num_nonconst: _,
                        attrs,
                        ..
                    } => {
                        if name == "::" {
                            self.print_object_literal(
                                level,
                                None,
                                elements.iter().enumerate(),
                                |this, (i, elem)| {
                                    match i {
                                        0 => this.write("hd"),
                                        1 => this.write("tl"),
                                        _ => {
                                            this.write("_");
                                            this.write(&i.to_string());
                                        }
                                    }
                                    this.write(": ");
                                    this.print_expression(elem, 1);
                                },
                            );
                        } else {
                            let untagged = tag_info_has_untagged(attrs);
                            if untagged && elements.len() == 1 {
                                self.print_expression(&elements[0], level);
                            } else {
                                let tag_name = tag_info_tag_name(attrs).unwrap_or("TAG");
                                let tag_value = tag_info_runtime_tag(attrs)
                                    .unwrap_or_else(|| SwitchCaseTag::String(name.clone()));
                                let include_tag = !untagged;
                                let include_debug_name =
                                    self.debug && !untagged && name.as_str() != "::";
                                self.print_object_literal(
                                    level,
                                    None,
                                    (if include_tag {
                                        vec![(None, None)]
                                    } else {
                                        Vec::new()
                                    })
                                    .into_iter()
                                    .chain(
                                        elements
                                            .iter()
                                            .enumerate()
                                            .map(|(i, elem)| (Some(i), Some(elem))),
                                    )
                                    .chain(
                                        include_debug_name
                                            .then_some((Some(usize::MAX), None))
                                            .into_iter(),
                                    ),
                                    |this, prop| match prop {
                                        (None, None) => {
                                            this.print_literal_property_name(tag_name);
                                            this.write(": ");
                                            this.print_switch_case_tag(&tag_value);
                                        }
                                        (Some(i), Some(elem)) => {
                                            this.write("_");
                                            this.write(&i.to_string());
                                            this.write(": ");
                                            this.print_expression(elem, 1);
                                        }
                                        (Some(i), None) if i == usize::MAX => {
                                            this.print_property_name(&PropertyName::Symbol);
                                            this.write(": ");
                                            this.print_string(name);
                                        }
                                        _ => unreachable!(
                                            "constructor literal properties stay aligned"
                                        ),
                                    },
                                );
                            }
                        }
                    }
                    TagInfo::PolyVar(_) => {
                        // OCaml's `js_dump.ml:901-912` for `Caml_block(el, _, _,
                        // Blk_poly_var _)` emits `{NAME: el[0]; VAL: el[1]}` —
                        // the NAME slot is whatever expression sits at
                        // elements[0] (a `Const_int n` for numeric polyvar
                        // names like `#1`, a `Const_string "Foo"` otherwise).
                        // Printing the `name` string verbatim as done
                        // previously emitted `NAME: "1"` for `#1` instead of
                        // `NAME: 1`.
                        self.print_object_literal(
                            level,
                            None,
                            std::iter::once((false, elements.first())).chain(
                                elements.get(1).into_iter().map(|value| (true, Some(value))),
                            ),
                            |this, (is_value, value)| {
                                let value = value.expect("polyvar block element must exist");
                                if is_value {
                                    this.write("VAL: ");
                                } else {
                                    this.write("NAME: ");
                                }
                                this.print_expression(value, 1);
                            },
                        );
                    }
                    _ => {
                        self.print_array_literal(elements);
                    }
                }
            }

            ExpressionDesc::CamlBlockTag(e, tag) => {
                self.with_indent(1, |this| this.print_expression(e, 15));
                self.write_char('.');
                self.write(tag);
            }
        }
    }

    fn try_print_exception_block(
        &mut self,
        expr: &Expression,
        level: u8,
        include_stack: bool,
    ) -> bool {
        match &expr.desc {
            ExpressionDesc::CamlBlock(elements, _, _, tag_info)
                if matches!(
                    tag_info,
                    crate::lambda::TagInfo::Extension | crate::lambda::TagInfo::RecordExt { .. }
                ) =>
            {
                self.print_exception_block_literal(level, elements, tag_info, include_stack);
                true
            }
            _ => false,
        }
    }

    fn print_exception_block_literal(
        &mut self,
        level: u8,
        elements: &[Expression],
        tag_info: &crate::lambda::TagInfo,
        include_stack: bool,
    ) {
        let mut props: Vec<(String, Option<&Expression>)> =
            Vec::with_capacity(elements.len() + usize::from(include_stack));
        for (index, element) in elements.iter().enumerate() {
            let name = match tag_info {
                crate::lambda::TagInfo::Extension => {
                    if index == 0 {
                        "RE_EXN_ID".to_string()
                    } else {
                        format!("_{index}")
                    }
                }
                crate::lambda::TagInfo::RecordExt { fields, .. } => {
                    if index == 0 {
                        "RE_EXN_ID".to_string()
                    } else {
                        fields
                            .get(index - 1)
                            .cloned()
                            .unwrap_or_else(|| format!("_{index}"))
                    }
                }
                _ => unreachable!("exception block printer only handles exception tag kinds"),
            };
            props.push((name, Some(element)));
        }
        if include_stack {
            props.push(("Error".to_string(), None));
        }

        self.print_object_literal(level, None, props.iter(), |this, prop| {
            let (name, value) = prop;
            this.print_literal_property_name(name);
            this.write(": ");
            if let Some(value) = value {
                this.print_expression(value, 1);
            } else {
                this.write("new Error()");
            }
        });
    }

    /// Print a variable identifier
    fn print_vident(&mut self, vident: &VIdent) {
        match vident {
            VIdent::Id(id) => {
                let name = self.ident_name(id);
                self.write(&name);
            }
            VIdent::Qualified(module, None) => {
                let mod_name = self.module_ident_name(&module.id);
                self.write(&mod_name);
            }
            VIdent::Qualified(module, Some(_))
                if matches!(&module.kind, Kind::External { default: true, .. }) =>
            {
                let mod_name = self.module_ident_name(&module.id);
                self.write(&mod_name);
            }
            VIdent::Qualified(module, Some(member)) => {
                let mod_name = self.module_ident_name(&module.id);
                self.write(&mod_name);
                match &module.kind {
                    Kind::Ml | Kind::Runtime => {
                        let printed_member = if member == "default" {
                            "default".to_string()
                        } else {
                            convert_ident_name(member)
                        };
                        self.write_char('.');
                        self.write(&printed_member);
                    }
                    Kind::External { .. } => {
                        self.print_property_access(member);
                    }
                }
            }
        }
    }

    fn print_object_literal<T, I, F>(
        &mut self,
        level: u8,
        dup: Option<&Expression>,
        props: I,
        mut print_prop: F,
    ) where
        I: IntoIterator<Item = T>,
        F: FnMut(&mut Self, T),
    {
        let needs_paren = level > 1;
        if needs_paren {
            self.write_char('(');
        }

        self.write_char('{');
        let mut props = props.into_iter().peekable();
        if let (Some(spread), None) = (dup, props.peek()) {
            self.write("...");
            self.print_expression(spread, 1);
        } else if dup.is_some() || props.peek().is_some() {
            self.indent();

            if let Some(spread) = dup {
                self.newline();
                self.write("...");
                self.print_expression(spread, 1);
                if props.peek().is_some() {
                    self.write_char(',');
                }
            }

            while let Some(prop) = props.next() {
                self.newline();
                print_prop(self, prop);
                if props.peek().is_some() {
                    self.write_char(',');
                }
            }

            self.dedent();
            self.newline();
        }
        self.write_char('}');

        if needs_paren {
            self.write_char(')');
        }
    }

    fn print_member_target_expression(&mut self, expr: &Expression, extra_group_indent: bool) {
        if extra_group_indent {
            self.indent();
        }
        self.print_expression(expr, 15);
        if extra_group_indent {
            self.dedent();
        }
    }

    fn print_dot_member_target_expression(&mut self, expr: &Expression) {
        self.suppress_member_target_call_arg_group_indent += 1;
        self.print_expression(expr, 15);
        self.suppress_member_target_call_arg_group_indent -= 1;
    }

    fn print_call_argument(&mut self, expr: &Expression, call_level: u8) {
        let extra_group_indent =
            call_argument_needs_extra_group_indent(expr, call_level, self.indent)
                && self.suppress_member_target_call_arg_group_indent == 0
                && !self.output.is_empty()
                && !self.last_new_line;
        if extra_group_indent {
            self.indent();
        }
        self.print_expression(expr, 1);
        if extra_group_indent {
            self.dedent();
        }
    }

    fn previous_non_space_char_on_line(&self) -> Option<char> {
        self.output
            .chars()
            .rev()
            .take_while(|c| *c != '\n')
            .find(|c| !c.is_whitespace())
    }

    fn print_array_literal(&mut self, elements: &[Expression]) {
        self.write_char('[');
        match elements {
            [] => {}
            [single] => self.with_indent(1, |this| this.print_expression(single, 1)),
            _ => {
                self.indent();
                for (index, elem) in elements.iter().enumerate() {
                    self.newline();
                    self.print_expression(elem, 1);
                    if index + 1 < elements.len() {
                        self.write_char(',');
                    }
                }
                self.dedent();
                self.newline();
            }
        }
        self.write_char(']');
    }

    fn print_literal_property_name(&mut self, name: &str) {
        let name = unwrap_uppercase_exotic(name);
        if property_access_uses_dot(name) {
            self.write(name);
        } else {
            self.print_string(name);
        }
    }

    /// Print a property name
    fn print_property_name(&mut self, name: &PropertyName) {
        match name {
            PropertyName::Lit(s) => self.print_literal_property_name(s),
            PropertyName::Symbol => {
                self.write("[Symbol.for(\"name\")]");
            }
        }
    }

    /// Print property access
    fn print_property_access(&mut self, name: &str) {
        let name = unwrap_uppercase_exotic(name);
        if property_access_uses_dot(name) {
            self.write_char('.');
            self.write(name);
        } else {
            self.write_char('[');
            match name.parse::<i64>() {
                Ok(index) if index.to_string() == name => self.write(name),
                _ => self.print_string(name),
            }
            self.write_char(']');
        }
    }

    /// Print a number
    fn print_number(&mut self, n: &Number, level: u8) {
        let s = match n {
            Number::Float(f) => normalize_float_literal_for_js(&f.f),
            Number::Int { i, c: Some(c) } => {
                format!("/* {} */{}", format_char_comment(*c), i)
            }
            Number::Int { i, c: None } => format!("{}", i),
            Number::BigInt(b) => {
                format!("{}{}n", if b.positive { "" } else { "-" }, b.value)
            }
        };

        // Negative numbers may need parens
        let needs_paren = (s.starts_with('-') && level > 13)
            || (level == 15 && !s.starts_with('I') && !s.starts_with('N'));

        if needs_paren {
            self.write_char('(');
        }
        self.write(&s);
        if needs_paren {
            self.write_char(')');
        }
    }

    /// Print a string literal
    pub(super) fn print_string(&mut self, s: &str) {
        if s.is_ascii() {
            self.write_char('"');
            let bytes = s.as_bytes();
            let mut chunk_start = 0;
            for (index, byte) in bytes.iter().copied().enumerate() {
                let escaped = match byte {
                    b'"' => Some("\\\""),
                    b'\\' => Some("\\\\"),
                    b'\n' => Some("\\n"),
                    b'\r' => Some("\\r"),
                    b'\t' => Some("\\t"),
                    0..=31 => {
                        if chunk_start < index {
                            self.write(&s[chunk_start..index]);
                        }
                        write!(self.output, "\\x{byte:02x}").unwrap();
                        self.last_new_line = false;
                        chunk_start = index + 1;
                        continue;
                    }
                    _ => None,
                };
                if let Some(escaped) = escaped {
                    if chunk_start < index {
                        self.write(&s[chunk_start..index]);
                    }
                    self.write(escaped);
                    chunk_start = index + 1;
                }
            }
            if chunk_start < s.len() {
                self.write(&s[chunk_start..]);
            }
            self.write_char('"');
            return;
        }

        let decoded = decode_internal_utf8_string(s);
        self.write_char('"');
        for c in decoded.chars() {
            match c {
                '"' => self.write("\\\""),
                '\\' => self.write("\\\\"),
                '\n' => self.write("\\n"),
                '\r' => self.write("\\r"),
                '\t' => self.write("\\t"),
                c if c < ' ' => {
                    write!(self.output, "\\x{:02x}", c as u32).unwrap();
                    self.last_new_line = false;
                }
                c => self.write_char(c),
            }
        }
        self.write_char('"');
    }

    /// Print a string with specific delimiter
    fn print_string_with_delim(&mut self, s: &str, delim: Delim) {
        match delim {
            Delim::None => self.print_string(s),
            Delim::NoQuotes => self.write_decoded_internal_string(s),
            Delim::BackQuotes => {
                self.write_char('`');
                self.write_decoded_internal_string(s);
                self.write_char('`');
            }
            Delim::StarJ => {
                self.write_char('"');
                self.write_decoded_internal_string(s);
                self.write_char('"');
            }
        }
    }

    pub(super) fn write_decoded_internal_string(&mut self, s: &str) {
        match decode_internal_utf8_string(s) {
            Cow::Borrowed(decoded) => self.write(decoded),
            Cow::Owned(decoded) => self.write(&decoded),
        }
    }

    /// Print raw JavaScript code
    fn print_raw_js(&mut self, info: &JsRawInfo) {
        if info.is_stmt {
            self.newline();
            self.write_decoded_internal_string(&info.code);
            self.newline();
        } else {
            let needs_paren = raw_js_expression_needs_paren(&info.code);
            if needs_paren {
                self.write_char('(');
            }
            self.write_decoded_internal_string(&info.code);
            if needs_paren {
                self.write_char(')');
            }
        }
    }

    /// Print a function body using the same return-unit elision rules as OCaml.
    fn print_function_body(&mut self, stmts: &Block, return_unit: bool) {
        if stmts.is_empty() {
            return;
        }

        if let Some(rewritten) =
            try_function_body_shared_success_disjunction_fallthrough_rewrite(stmts)
        {
            self.print_function_body(&rewritten, return_unit);
            return;
        }

        if let Some(rewritten) =
            try_function_body_shared_success_else_if_chain_suffix_rewrite(stmts)
        {
            self.print_function_body(&rewritten, return_unit);
            return;
        }

        if let Some(rewritten) = try_function_body_shared_return_guard_chain_suffix_rewrite(stmts) {
            self.print_function_body(&rewritten, return_unit);
            return;
        }

        if let Some(rewritten) =
            try_function_body_positive_strict_undefined_tail_suffix_rewrite(stmts)
        {
            self.print_function_body(&rewritten, return_unit);
            return;
        }

        // Leave guard-return fallthroughs as sibling statements, matching
        // compiler/core/js_stmt_make.ml:249-250.
        if let Some(rewritten) = try_function_body_drop_dead_undefined_binding_guard_prefix(stmts) {
            self.print_function_body(&rewritten, return_unit);
            return;
        }

        if return_unit {
            if let Some(merged) = try_unit_function_body_single_clean_negative_guard_merge(stmts) {
                self.print_function_tail_statement(&merged, return_unit);
                return;
            }
        }

        if let Some(merged) = try_function_body_shared_return_guard_chain_merge(stmts) {
            self.print_function_tail_statement(&merged, return_unit);
            return;
        }

        // OCaml's `function_body` only drops/elides unit tails while walking
        // statements; it does not rewrite early-return guard chains into a
        // positive success guard (compiler/core/js_dump.ml:1675-1703).

        if return_unit {
            let implicit_return = Statement::return_(Expression::undefined(true));

            if let [stmt, trailing_stmt] = stmts.as_slice() {
                if let Some(merged) = try_function_body_shared_tail_nested_if_merge(
                    stmt,
                    trailing_stmt,
                    &implicit_return,
                ) {
                    self.print_function_tail_statement(&merged, return_unit);
                    return;
                }

                if let Some(merged) = try_function_body_shared_tail_outer_else_merge(
                    stmt,
                    trailing_stmt,
                    &implicit_return,
                ) {
                    self.print_function_tail_statement(&merged, return_unit);
                    return;
                }
            }
        }

        if let [stmt, trailing_stmt, trailing_return] = stmts.as_slice() {
            if return_is_undefined(trailing_return) {
                if let Some(merged) = try_function_body_shared_tail_nested_if_merge(
                    stmt,
                    trailing_stmt,
                    trailing_return,
                ) {
                    self.print_function_tail_statement(&merged, return_unit);
                    return;
                }

                if let Some(merged) = try_function_body_shared_tail_outer_else_merge(
                    stmt,
                    trailing_stmt,
                    trailing_return,
                ) {
                    self.print_function_tail_statement(&merged, return_unit);
                    return;
                }
            }
        }

        if let [stmt, trailing_return] = stmts.as_slice() {
            if return_is_undefined(trailing_return) {
                if let Some(merged) =
                    try_function_body_trailing_return_nested_if_merge(stmt, trailing_return)
                {
                    self.print_function_tail_statement(&merged, return_unit);
                    return;
                }
            }
        }

        let mut printed_any = false;
        for (index, stmt) in stmts.iter().enumerate() {
            let printed = if index + 1 == stmts.len() {
                function_tail_statement_prints(stmt)
            } else {
                true
            };
            if !printed {
                continue;
            }
            if printed_any {
                self.newline();
            }
            if index + 1 == stmts.len() {
                self.print_function_tail_statement(stmt, return_unit);
            } else {
                self.print_statement(stmt, false);
            }
            printed_any = true;
        }
    }

    fn print_function_tail_statement(&mut self, stmt: &Statement, return_unit: bool) {
        // OCaml's `function_body` keeps guard chains as emitted by `S.if_`;
        // see compiler/core/js_dump.ml:1675-1703.

        if return_unit {
            if let Some(merged) = try_unit_function_tail_shared_else_guard_chain_merge(stmt) {
                self.print_function_tail_statement(&merged, return_unit);
                return;
            }

            if let Some(merged) = try_unit_function_tail_shared_else_positive_guard_merge(stmt) {
                self.print_function_tail_statement(&merged, return_unit);
                return;
            }

            if let Some(merged) = try_unit_function_tail_shared_else_guard_merge(stmt) {
                self.print_function_tail_statement(&merged, return_unit);
                return;
            }
        }

        match &stmt.desc {
            StatementDesc::Block(inner) if inner.len() == 1 => {
                self.print_function_tail_statement(&inner[0], return_unit);
            }
            StatementDesc::If(cond, then_, else_)
                if else_.is_empty()
                    && return_unit
                    && try_tail_nested_negative_guard_merge(then_).is_some() =>
            {
                let (inner_cond, inner_body) =
                    try_tail_nested_negative_guard_merge(then_).expect("checked above");
                self.print_function_tail_statement(
                    &Statement {
                        desc: StatementDesc::If(
                            Expression::bin(
                                BinOp::And,
                                cond.clone(),
                                negate_tail_merge_condition(&inner_cond),
                            ),
                            inner_body,
                            vec![],
                        ),
                        comment: stmt.comment.clone(),
                    },
                    return_unit,
                );
            }
            StatementDesc::If(cond, then_, else_)
                if else_.is_empty() && try_tail_nested_if_merge(then_, return_unit).is_some() =>
            {
                let (inner_cond, inner_then, inner_else) =
                    try_tail_nested_if_merge(then_, return_unit).expect("checked above");
                self.print_function_tail_statement(
                    &Statement {
                        desc: StatementDesc::If(
                            Expression::bin(BinOp::And, cond.clone(), inner_cond),
                            inner_then,
                            inner_else,
                        ),
                        comment: stmt.comment.clone(),
                    },
                    return_unit,
                );
            }
            StatementDesc::If(cond, then_, else_)
                if else_is_single_return_undefined(else_)
                    && try_tail_nested_if_merge_with_outer_undefined_else(then_).is_some() =>
            {
                let (inner_cond, inner_then, inner_else) =
                    try_tail_nested_if_merge_with_outer_undefined_else(then_)
                        .expect("checked above");
                self.print_function_tail_statement(
                    &Statement {
                        desc: StatementDesc::If(
                            Expression::bin(BinOp::And, cond.clone(), inner_cond),
                            inner_then,
                            inner_else,
                        ),
                        comment: stmt.comment.clone(),
                    },
                    return_unit,
                );
            }
            StatementDesc::If(cond, then_, else_) if else_is_single_return_undefined(else_) => {
                self.print_statement(
                    &Statement {
                        desc: StatementDesc::If(cond.clone(), then_.clone(), vec![]),
                        comment: stmt.comment.clone(),
                    },
                    false,
                );
            }
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Undefined { .. },
                ..
            }) => {}
            StatementDesc::Return(expr) if return_unit => {
                self.print_statement(
                    &Statement {
                        desc: StatementDesc::Exp(expr.clone()),
                        comment: stmt.comment.clone(),
                    },
                    false,
                );
            }
            _ => self.print_statement(stmt, false),
        }
    }
}

fn unwrap_single_block_stmt(stmt: &Statement) -> &Statement {
    match &stmt.desc {
        StatementDesc::Block(inner) if inner.len() == 1 => unwrap_single_block_stmt(&inner[0]),
        _ => stmt,
    }
}

/// Direct port of the eta-reduction check in OCaml's `pp_function`
/// (compiler/core/js_dump.ml:299-344). Returns the callee to print when the
/// function body is `[ Return (Call (Var v, args, _)) ]`, every argument is the
/// matching parameter, and call info permits the rewrite.
fn eta_reduce_function_body<'a>(
    is_method: bool,
    params: &[Ident],
    body: &'a Block,
) -> Option<&'a VIdent> {
    if is_method {
        return None;
    }
    let [stmt] = body.as_slice() else {
        return None;
    };
    let StatementDesc::Return(ret_expr) = &stmt.desc else {
        return None;
    };
    let ExpressionDesc::Call(callee, args, info) = &ret_expr.desc else {
        return None;
    };
    let ExpressionDesc::Var(v) = &callee.desc else {
        return None;
    };
    if args.len() != params.len() {
        return None;
    }
    for (arg, param) in args.iter().zip(params.iter()) {
        let ExpressionDesc::Var(VIdent::Id(arg_id)) = &arg.desc else {
            return None;
        };
        if !arg_id.same(param) {
            return None;
        }
    }
    // compiler/core/js_dump.ml:309-313 requires `arity = Full | NA` and
    // `call_info = Call_ml | Call_builtin_runtime`. Rust does not emit the
    // Curry wrapper used for `arity = NA` (js_dump.ml:331-343), so keep the
    // reduction to the exact `Full` case.
    if !matches!(info.kind, CallKind::MlCall | CallKind::BuiltinRuntime)
        || !matches!(info.arity, CallArity::Full)
    {
        return None;
    }

    match v {
        VIdent::Id(callee_id) => {
            if params.iter().any(|p| p.same(callee_id)) {
                return None;
            }
        }
        VIdent::Qualified(_, _) => {}
    }
    Some(v)
}

fn try_tail_nested_if_merge(
    block: &Block,
    allow_empty_else: bool,
) -> Option<(Expression, Block, Block)> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    match &stmt.desc {
        StatementDesc::Block(inner) => try_tail_nested_if_merge(inner, allow_empty_else),
        StatementDesc::If(cond, then_, else_)
            if else_is_single_return_undefined(else_) || (allow_empty_else && else_.is_empty()) =>
        {
            Some((cond.clone(), then_.clone(), else_.clone()))
        }
        _ => None,
    }
}

fn try_tail_nested_if_merge_with_outer_undefined_else(
    then_block: &Block,
) -> Option<(Expression, Block, Block)> {
    let (inner_cond, inner_then, inner_else) = try_tail_nested_if_merge(then_block, true)?;
    if !inner_else.is_empty() && !return_is_undefined_block(&inner_else) {
        return None;
    }

    Some((
        inner_cond,
        inner_then,
        if inner_else.is_empty() {
            vec![Statement::return_(Expression::undefined(true))]
        } else {
            inner_else
        },
    ))
}

fn try_tail_nested_negative_guard_merge(block: &Block) -> Option<(Expression, Block)> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    let StatementDesc::If(cond, then_, else_) = &unwrap_single_block_stmt(stmt).desc else {
        return None;
    };
    if !return_is_undefined_block(then_) || else_.is_empty() {
        return None;
    }

    Some((cond.clone(), else_.clone()))
}

fn try_function_body_trailing_return_nested_if_merge(
    stmt: &Statement,
    trailing_return: &Statement,
) -> Option<Statement> {
    if !return_is_undefined(trailing_return) {
        return None;
    }

    match &stmt.desc {
        StatementDesc::Block(inner) if inner.len() == 1 => {
            try_function_body_trailing_return_nested_if_merge(&inner[0], trailing_return)
        }
        StatementDesc::If(cond, then_, else_) if else_.is_empty() => {
            let (inner_cond, inner_then, inner_else) = try_tail_nested_if_merge(then_, true)?;
            if !inner_else.is_empty() && !return_is_undefined_block(&inner_else) {
                return None;
            }
            Some(Statement {
                desc: StatementDesc::If(
                    Expression::bin(BinOp::And, cond.clone(), inner_cond),
                    inner_then,
                    vec![],
                ),
                comment: stmt.comment.clone(),
            })
        }
        _ => None,
    }
}

fn try_function_body_shared_tail_nested_if_merge(
    stmt: &Statement,
    trailing_stmt: &Statement,
    trailing_return: &Statement,
) -> Option<Statement> {
    let stmt = unwrap_single_block_stmt(stmt);
    let StatementDesc::If(cond, then_, else_) = &stmt.desc else {
        return None;
    };
    if !else_.is_empty() {
        return None;
    }

    let [nested_stmt] = then_.as_slice() else {
        return None;
    };
    let nested_stmt = unwrap_single_block_stmt(nested_stmt);
    let StatementDesc::If(inner_cond, inner_then, inner_else) = &nested_stmt.desc else {
        return None;
    };
    if !inner_else.is_empty() {
        return None;
    }

    Some(Statement {
        desc: StatementDesc::If(
            cond.clone(),
            vec![
                Statement::new(StatementDesc::If(
                    inner_cond.clone(),
                    inner_then.clone(),
                    vec![],
                )),
                trailing_stmt.clone(),
                trailing_return.clone(),
            ],
            vec![trailing_stmt.clone(), trailing_return.clone()],
        ),
        comment: stmt.comment.clone(),
    })
}

fn try_function_body_shared_tail_outer_else_merge(
    stmt: &Statement,
    trailing_stmt: &Statement,
    trailing_return: &Statement,
) -> Option<Statement> {
    let stmt = unwrap_single_block_stmt(stmt);
    let StatementDesc::If(cond, then_, else_) = &stmt.desc else {
        return None;
    };
    if !else_.is_empty() {
        return None;
    }

    let shared_tail = vec![trailing_stmt.clone(), trailing_return.clone()];
    let stripped_then = strip_trailing_return_undefined_block(then_)?;
    if stripped_then.is_empty() {
        return None;
    }

    match unwrap_single_block_stmt(&then_[0]).desc {
        StatementDesc::If(_, _, _) => Some(Statement {
            desc: StatementDesc::If(cond.clone(), then_.clone(), shared_tail),
            comment: stmt.comment.clone(),
        }),
        _ => None,
    }
}

fn try_unit_function_tail_shared_else_guard_chain_merge(stmt: &Statement) -> Option<Statement> {
    let stmt = unwrap_single_block_stmt(stmt);
    let StatementDesc::If(outer_cond, then_block, else_block) = &stmt.desc else {
        return None;
    };
    let stripped_else = strip_trailing_return_undefined_block(else_block)?;
    if stripped_else.is_empty() {
        return None;
    }

    let (first_then, remaining_then) = then_block.split_first()?;
    if !ocaml_eq_block(&remaining_then.to_vec(), else_block) {
        return None;
    }

    let StatementDesc::If(inner_cond, inner_then, inner_else) =
        &unwrap_single_block_stmt(first_then).desc
    else {
        return None;
    };
    if !inner_else.is_empty() {
        return None;
    }

    let (guard_cond, stripped_then) =
        strip_leading_negative_guard_shared_else(inner_then, else_block)?;

    Some(Statement::new(StatementDesc::If(
        Expression::bin(
            BinOp::And,
            Expression::bin(BinOp::And, outer_cond.clone(), inner_cond.clone()),
            negate_tail_merge_condition(&guard_cond),
        ),
        stripped_then,
        stripped_else,
    )))
}

fn try_unit_function_tail_shared_else_guard_merge(stmt: &Statement) -> Option<Statement> {
    let stmt = unwrap_single_block_stmt(stmt);
    let StatementDesc::If(outer_cond, then_block, else_block) = &stmt.desc else {
        return None;
    };
    let stripped_else = strip_trailing_return_undefined_block(else_block)?;
    if stripped_else.is_empty() {
        return None;
    }

    let (first_then, remaining_then) = then_block.split_first()?;
    let StatementDesc::If(inner_cond, inner_then, inner_else) =
        &unwrap_single_block_stmt(first_then).desc
    else {
        return None;
    };
    if !inner_else.is_empty() || !ocaml_eq_block(inner_then, else_block) {
        return None;
    }

    let stripped_then = strip_trailing_return_undefined_block(&remaining_then.to_vec())?;
    if stripped_then.is_empty() {
        return None;
    }

    Some(Statement::new(StatementDesc::If(
        Expression::bin(
            BinOp::And,
            outer_cond.clone(),
            negate_tail_merge_condition(inner_cond),
        ),
        stripped_then,
        stripped_else,
    )))
}

fn try_unit_function_tail_shared_else_positive_guard_merge(stmt: &Statement) -> Option<Statement> {
    let stmt = unwrap_single_block_stmt(stmt);
    let StatementDesc::If(outer_cond, then_block, else_block) = &stmt.desc else {
        return None;
    };
    let stripped_else = strip_trailing_return_undefined_block(else_block)?;
    if stripped_else.is_empty() {
        return None;
    }

    let (first_then, remaining_then) = then_block.split_first()?;
    let StatementDesc::If(inner_cond, inner_then, inner_else) =
        &unwrap_single_block_stmt(first_then).desc
    else {
        return None;
    };
    if !inner_else.is_empty() || !ocaml_eq_block(&remaining_then.to_vec(), else_block) {
        return None;
    }

    let stripped_then = strip_trailing_return_undefined_block(inner_then)?;
    if stripped_then.is_empty() {
        return None;
    }

    if !positive_guard_merge_outer_cond_is_redundant(outer_cond, inner_cond) {
        return None;
    }
    let combined_cond = Expression::bin(BinOp::And, outer_cond.clone(), inner_cond.clone());

    Some(Statement::new(StatementDesc::If(
        combined_cond,
        stripped_then,
        stripped_else,
    )))
}

fn positive_guard_merge_outer_cond_is_redundant(
    outer_cond: &Expression,
    inner_cond: &Expression,
) -> bool {
    matches!(
        (&outer_cond.desc, &inner_cond.desc),
        (
            ExpressionDesc::Bin(BinOp::NotEqEq, outer_lhs, outer_rhs),
            ExpressionDesc::Bin(BinOp::EqEqEq, inner_lhs, inner_rhs),
        ) if matches!(
            (
                &outer_lhs.as_ref().desc,
                &outer_rhs.as_ref().desc,
                &inner_lhs.as_ref().desc,
                &inner_rhs.as_ref().desc,
            ),
            (
                ExpressionDesc::Var(VIdent::Id(outer_id)),
                ExpressionDesc::Undefined { .. },
                ExpressionDesc::Var(VIdent::Id(inner_id)),
                ExpressionDesc::Str { .. } | ExpressionDesc::Number(_),
            ) if outer_id.same(inner_id)
        )
    )
}

fn strip_trailing_return_undefined_block(block: &Block) -> Option<Block> {
    let (tail, body) = block.split_last()?;
    if !return_is_undefined(unwrap_single_block_stmt(tail)) {
        return None;
    }
    Some(body.to_vec())
}

fn strip_leading_negative_guard_shared_else(
    block: &Block,
    else_block: &Block,
) -> Option<(Expression, Block)> {
    let (first, remaining) = block.split_first()?;
    let StatementDesc::If(cond, then_block, else_block_inner) =
        &unwrap_single_block_stmt(first).desc
    else {
        return None;
    };
    if !else_block_inner.is_empty() || !ocaml_eq_block(then_block, else_block) {
        return None;
    }

    let stripped_block = strip_trailing_return_undefined_block(&remaining.to_vec())?;
    if stripped_block.is_empty() {
        return None;
    }

    Some((cond.clone(), stripped_block))
}

fn try_unit_function_body_single_clean_negative_guard_merge(stmts: &Block) -> Option<Statement> {
    let mut guards = Vec::new();
    let mut body = collect_function_tail_negative_guard_chain_stmt(
        &Statement::new(StatementDesc::Block(stmts.clone())),
        &mut guards,
    )?;
    if body.is_empty() {
        return None;
    }

    let [guard] = guards.as_slice() else {
        return None;
    };
    let positive_guard = supported_single_negative_guard_condition(guard)?;
    if !supported_single_negative_guard_body(&body) {
        return None;
    }

    if !body
        .last()
        .is_some_and(|stmt| return_is_undefined(unwrap_single_block_stmt(stmt)))
    {
        body.push(Statement::return_(Expression::undefined(true)));
    }

    Some(Statement::new(StatementDesc::If(
        positive_guard,
        body,
        vec![],
    )))
}

fn try_function_body_shared_return_guard_chain_merge(stmts: &[Statement]) -> Option<Statement> {
    let (last, prefix) = stmts.split_last()?;
    if prefix.is_empty() {
        return None;
    }

    let mut fallback: Option<Expression> = None;
    let mut positive_guards = Vec::new();

    for stmt in prefix {
        let guard = shared_return_guard_test(stmt, &mut fallback)?;
        positive_guards.push(negate_tail_merge_condition(&guard));
    }

    let (final_guard, success_block) =
        shared_return_guard_chain_terminal_success(last, &mut fallback)?;
    if success_block.is_empty() {
        return None;
    }
    positive_guards.push(final_guard);

    let fallback = fallback?;
    let mut guards = positive_guards.into_iter();
    let cond = guards.next()?;
    let cond = guards.fold(cond, |acc, guard| Expression::bin(BinOp::And, acc, guard));

    Some(Statement {
        desc: StatementDesc::If(cond, success_block, vec![Statement::return_(fallback)]),
        comment: None,
    })
}

fn try_function_body_shared_return_guard_chain_suffix_rewrite(stmts: &Block) -> Option<Block> {
    if stmts.len() < 2 {
        return None;
    }

    for start in 0..stmts.len() - 1 {
        let suffix = &stmts[start..];
        if let Some(merged) = try_function_body_shared_return_guard_chain_merge(suffix) {
            let mut rewritten = stmts[..start].to_vec();
            rewritten.push(merged);
            return Some(rewritten);
        }
    }

    None
}

fn try_function_body_positive_strict_undefined_tail_if_rewrite(
    stmts: &[Statement],
) -> Option<Statement> {
    let [guard_stmt, success_stmt] = stmts else {
        return None;
    };

    let StatementDesc::If(test, then_, else_) = &unwrap_single_block_stmt(guard_stmt).desc else {
        return None;
    };
    if !else_.is_empty() {
        return None;
    }

    let positive_test = negate_positive_strict_undefined_guard(test)?;
    let fallback = single_wrapped_return_expr(then_)?;
    if matches!(fallback.desc, ExpressionDesc::Undefined { .. }) {
        return None;
    }

    let success_stmt = unwrap_single_block_stmt(success_stmt);
    let success_supported = matches!(success_stmt.desc, StatementDesc::Return(_))
        || stmt_is_simple_total_return_if(success_stmt);
    if !success_supported {
        return None;
    }

    Some(Statement {
        desc: StatementDesc::If(
            positive_test,
            vec![success_stmt.clone()],
            vec![Statement::return_(fallback.clone())],
        ),
        comment: guard_stmt.comment.clone(),
    })
}

fn try_function_body_positive_strict_undefined_tail_suffix_rewrite(stmts: &Block) -> Option<Block> {
    if stmts.len() < 2 {
        return None;
    }

    for start in 0..stmts.len() - 1 {
        let suffix = &stmts[start..];
        if let Some(rewritten_stmt) =
            try_function_body_positive_strict_undefined_tail_if_rewrite(suffix)
        {
            let mut rewritten = stmts[..start].to_vec();
            rewritten.push(rewritten_stmt);
            return Some(rewritten);
        }
    }

    None
}

fn negate_positive_strict_undefined_guard(cond: &Expression) -> Option<Expression> {
    match &cond.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right)
            if matches!(right.as_ref().desc, ExpressionDesc::Undefined { .. }) =>
        {
            Some(Expression::bin(
                BinOp::NotEqEq,
                left.as_ref().clone(),
                right.as_ref().clone(),
            ))
        }
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right)
            if matches!(left.as_ref().desc, ExpressionDesc::Undefined { .. }) =>
        {
            Some(Expression::bin(
                BinOp::NotEqEq,
                right.as_ref().clone(),
                left.as_ref().clone(),
            ))
        }
        _ => None,
    }
}

fn stmt_is_simple_total_return_if(stmt: &Statement) -> bool {
    let StatementDesc::If(_, then_, else_) = &unwrap_single_block_stmt(stmt).desc else {
        return false;
    };

    single_wrapped_return_expr(then_).is_some() && single_wrapped_return_expr(else_).is_some()
}

fn try_function_body_shared_success_else_if_chain_suffix_rewrite(stmts: &Block) -> Option<Block> {
    let (last, prefix) = stmts.split_last()?;
    let (cond, fallback, success) = shared_success_else_if_chain(last)?;

    let mut rewritten = prefix.to_vec();
    rewritten.push(Statement {
        desc: StatementDesc::If(cond, vec![Statement::return_(fallback)], vec![]),
        comment: last.comment.clone(),
    });
    rewritten.push(Statement::return_(success));
    Some(rewritten)
}

fn try_function_body_shared_success_disjunction_fallthrough_rewrite(
    stmts: &Block,
) -> Option<Block> {
    let (last, prefix) = stmts.split_last()?;
    let stmt = unwrap_single_block_stmt(last);
    let StatementDesc::If(cond, then_, else_) = &stmt.desc else {
        return None;
    };

    let success = single_wrapped_return_expr(then_)?;
    let fallback = single_wrapped_return_expr(else_)?;
    if ocaml_eq_expression(success, fallback) {
        return None;
    }

    let cond = positive_conjunction_from_disjunction_chain(cond)?;

    let mut rewritten = prefix.to_vec();
    rewritten.push(Statement {
        desc: StatementDesc::If(cond, vec![Statement::return_(fallback.clone())], vec![]),
        comment: last.comment.clone(),
    });
    rewritten.push(Statement::return_(success.clone()));
    Some(rewritten)
}

fn shared_success_else_if_chain(stmt: &Statement) -> Option<(Expression, Expression, Expression)> {
    let mut guards = Vec::new();
    let mut success: Option<Expression> = None;
    let fallback = collect_shared_success_else_if_chain(stmt, &mut guards, &mut success)?;
    if guards.len() < 2 {
        return None;
    }

    let mut positive_guards = guards
        .into_iter()
        .map(|guard| negate_tail_merge_condition(&guard));
    let cond = positive_guards.next()?;
    let cond = positive_guards.fold(cond, |acc, guard| Expression::bin(BinOp::And, acc, guard));

    Some((cond, fallback, success?))
}

fn positive_conjunction_from_disjunction_chain(cond: &Expression) -> Option<Expression> {
    let mut guards = Vec::new();
    collect_disjunction_chain(cond, &mut guards);
    if guards.len() < 2 || !guards.iter().all(disjunction_guard_is_nonzero_zero_test) {
        return None;
    }

    let mut positive_guards = guards
        .into_iter()
        .map(|guard| negate_tail_merge_condition(&guard));
    let cond = positive_guards.next()?;
    Some(positive_guards.fold(cond, |acc, guard| Expression::bin(BinOp::And, acc, guard)))
}

fn disjunction_guard_is_nonzero_zero_test(cond: &Expression) -> bool {
    matches!(
        &cond.desc,
        ExpressionDesc::Bin(BinOp::NotEqEq, left, right)
            if is_zero_int_literal(left) || is_zero_int_literal(right)
    )
}

fn is_zero_int_literal(expr: &Expression) -> bool {
    matches!(expr.desc, ExpressionDesc::Number(Number::Int { i: 0, .. }))
}

fn collect_disjunction_chain(cond: &Expression, guards: &mut Vec<Expression>) {
    match &cond.desc {
        ExpressionDesc::Bin(BinOp::Or, left, right) => {
            collect_disjunction_chain(left, guards);
            collect_disjunction_chain(right, guards);
        }
        _ => guards.push(cond.clone()),
    }
}

fn collect_shared_success_else_if_chain(
    stmt: &Statement,
    guards: &mut Vec<Expression>,
    success: &mut Option<Expression>,
) -> Option<Expression> {
    let stmt = unwrap_single_block_stmt(stmt);
    let StatementDesc::If(cond, then_, else_) = &stmt.desc else {
        return None;
    };

    let then_return = single_wrapped_return_expr(then_)?;
    match success {
        Some(existing) if !ocaml_eq_expression(existing, then_return) => return None,
        Some(_) => {}
        None => {
            *success = Some(then_return.clone());
        }
    }

    guards.push(cond.clone());

    if let Some(fallback) = single_wrapped_return_expr(else_) {
        if success
            .as_ref()
            .is_some_and(|existing| ocaml_eq_expression(existing, fallback))
        {
            return None;
        }
        return Some(fallback.clone());
    }

    let nested = single_else_if_stmt_like_ocaml(else_)?;
    collect_shared_success_else_if_chain(nested, guards, success)
}

fn collect_function_tail_negative_guard_chain_stmt(
    stmt: &Statement,
    guards: &mut Vec<Expression>,
) -> Option<Block> {
    match &stmt.desc {
        StatementDesc::Block(inner) => {
            collect_function_tail_negative_guard_chain_block(inner, guards)
        }
        _ if guards.is_empty() => None,
        _ => Some(vec![stmt.clone()]),
    }
}

fn collect_function_tail_negative_guard_chain_block(
    block: &Block,
    guards: &mut Vec<Expression>,
) -> Option<Block> {
    match block.as_slice() {
        [] => None,
        [stmt] => collect_function_tail_negative_guard_chain_stmt(stmt, guards),
        [first, rest @ ..] => {
            if let Some(test) = negative_guard_return_undefined_test(first) {
                guards.push(Expression::not(test.clone()));
                collect_function_tail_negative_guard_chain_stmt(
                    &Statement::new(StatementDesc::Block(rest.to_vec())),
                    guards,
                )
            } else if guards.is_empty() {
                None
            } else {
                Some(block.clone())
            }
        }
    }
}

fn try_function_body_drop_dead_undefined_binding_guard_prefix(stmts: &Block) -> Option<Block> {
    match stmts.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => {
            return try_function_body_drop_dead_undefined_binding_guard_prefix(inner);
        }
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
            rest @ ..,
        ] => {
            let mut flattened = inner.clone();
            flattened.extend(rest.iter().cloned());
            if let Some(rewritten) =
                try_function_body_drop_dead_undefined_binding_guard_prefix(&flattened)
            {
                return Some(rewritten);
            }
        }
        _ => {}
    }

    let [decl_stmt, if_stmt, rest @ ..] = stmts.as_slice() else {
        return None;
    };

    let StatementDesc::Variable(decl) = &decl_stmt.desc else {
        return None;
    };
    if decl.value.is_some() || block_mentions_ident(rest, &decl.ident) {
        return None;
    }

    let StatementDesc::If(cond, then_block, else_block) = &unwrap_single_block_stmt(if_stmt).desc
    else {
        return None;
    };

    if block_is_single_wrapped_assign_undefined_to_ident(then_block, &decl.ident)
        && block_terminates_without_ident(else_block, &decl.ident)
    {
        let mut rewritten = Vec::with_capacity(stmts.len().saturating_sub(1));
        rewritten.push(Statement {
            desc: StatementDesc::If(
                negate_tail_merge_condition(cond),
                else_block.clone(),
                vec![],
            ),
            comment: decl_stmt
                .comment
                .clone()
                .or_else(|| if_stmt.comment.clone()),
        });
        rewritten.extend(rest.iter().cloned());
        return Some(rewritten);
    }

    if block_is_single_wrapped_assign_undefined_to_ident(else_block, &decl.ident)
        && block_terminates_without_ident(then_block, &decl.ident)
    {
        let mut rewritten = Vec::with_capacity(stmts.len().saturating_sub(1));
        rewritten.push(Statement {
            desc: StatementDesc::If(cond.clone(), then_block.clone(), vec![]),
            comment: decl_stmt
                .comment
                .clone()
                .or_else(|| if_stmt.comment.clone()),
        });
        rewritten.extend(rest.iter().cloned());
        return Some(rewritten);
    }

    None
}

fn block_is_single_wrapped_assign_undefined_to_ident(block: &Block, ident: &Ident) -> bool {
    matches!(
        block.as_slice(),
        [stmt] if assigns_undefined_to_ident(unwrap_single_block_stmt(stmt), ident)
    )
}

fn assigns_undefined_to_ident(stmt: &Statement, ident: &Ident) -> bool {
    matches!(
        &stmt.desc,
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(
                BinOp::Eq,
                lhs,
                rhs,
            ),
            ..
        }) if matches!(
            (&lhs.as_ref().desc, &rhs.as_ref().desc),
            (
                ExpressionDesc::Var(VIdent::Id(target)),
                ExpressionDesc::Undefined { .. },
            ) if target.same(ident)
        )
    )
}

fn block_terminates_without_ident(block: &Block, ident: &Ident) -> bool {
    !block.is_empty() && block_terminates(block) && !block_mentions_ident(block, ident)
}

fn block_terminates(block: &Block) -> bool {
    block.last().is_some_and(statement_terminates)
}

fn statement_terminates(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Block(inner) => block_terminates(inner),
        StatementDesc::Return(_)
        | StatementDesc::Throw(_)
        | StatementDesc::Break(_)
        | StatementDesc::Continue(_) => true,
        _ => false,
    }
}

fn block_mentions_ident(block: &[Statement], ident: &Ident) -> bool {
    block
        .iter()
        .any(|stmt| statement_mentions_ident(stmt, ident))
}

fn statement_mentions_ident(stmt: &Statement, ident: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(inner) => block_mentions_ident(inner, ident),
        StatementDesc::Variable(VariableDeclaration {
            ident: binding,
            value,
            ..
        }) => {
            binding.same(ident)
                || value
                    .as_ref()
                    .is_some_and(|value| expression_mentions_ident(value, ident))
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_mentions_ident(expr, ident)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_mentions_ident(cond, ident)
                || block_mentions_ident(then_block, ident)
                || block_mentions_ident(else_block, ident)
        }
        StatementDesc::While(_, cond, body) => {
            expression_mentions_ident(cond, ident) || block_mentions_ident(body, ident)
        }
        StatementDesc::ForRange(_, start, finish, loop_ident, _, body) => {
            loop_ident.same(ident)
                || start
                    .as_ref()
                    .is_some_and(|start| expression_mentions_ident(start, ident))
                || expression_mentions_ident(finish, ident)
                || block_mentions_ident(body, ident)
        }
        StatementDesc::ForOf(_, loop_ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, loop_ident, iterable, body) => {
            loop_ident.same(ident)
                || expression_mentions_ident(iterable, ident)
                || block_mentions_ident(body, ident)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_mentions_ident(test, ident)
                || clauses
                    .iter()
                    .any(|(_, clause)| block_mentions_ident(&clause.body, ident))
                || default
                    .as_ref()
                    .is_some_and(|block| block_mentions_ident(block, ident))
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_mentions_ident(test, ident)
                || clauses
                    .iter()
                    .any(|clause| block_mentions_ident(&clause.clause.body, ident))
                || default
                    .as_ref()
                    .is_some_and(|block| block_mentions_ident(block, ident))
        }
        StatementDesc::Try(body, catch, finally) => {
            block_mentions_ident(body, ident)
                || catch.as_ref().is_some_and(|(catch_ident, catch_block)| {
                    catch_ident.same(ident) || block_mentions_ident(catch_block, ident)
                })
                || finally
                    .as_ref()
                    .is_some_and(|block| block_mentions_ident(block, ident))
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => false,
    }
}

fn expression_mentions_ident(expr: &Expression, ident: &Ident) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(binding)) => binding.same(ident),
        ExpressionDesc::Var(VIdent::Qualified(_, _))
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::RawJsCode(_) => false,
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::New(inner, None) => expression_mentions_ident(inner, ident),
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_mentions_ident(left, ident) || expression_mentions_ident(right, ident)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_mentions_ident(test, ident)
                || expression_mentions_ident(consequent, ident)
                || expression_mentions_ident(alternate, ident)
        }
        ExpressionDesc::Call(func, args, _)
        | ExpressionDesc::New(func, Some(args))
        | ExpressionDesc::TaggedTemplate(func, _, args) => {
            expression_mentions_ident(func, ident)
                || args.iter().any(|arg| expression_mentions_ident(arg, ident))
        }
        ExpressionDesc::Fun { params, body, .. } => {
            params.iter().any(|param| param.same(ident)) || block_mentions_ident(body, ident)
        }
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_mentions_ident(item, ident)),
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            expression_mentions_ident(tag, ident)
                || items
                    .iter()
                    .any(|item| expression_mentions_ident(item, ident))
        }
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref()
                .is_some_and(|dup| expression_mentions_ident(dup, ident))
                || props
                    .iter()
                    .any(|(_, value)| expression_mentions_ident(value, ident))
        }
    }
}

fn negative_guard_return_undefined_test(stmt: &Statement) -> Option<&Expression> {
    match &unwrap_single_block_stmt(stmt).desc {
        StatementDesc::If(test, then_, else_)
            if block_is_single_wrapped_return_undefined(then_) && else_.is_empty() =>
        {
            Some(test)
        }
        _ => None,
    }
}

fn block_is_single_wrapped_return_undefined(block: &Block) -> bool {
    matches!(block.as_slice(), [stmt] if return_is_undefined(unwrap_single_block_stmt(stmt)))
}

fn single_wrapped_return_expr(block: &Block) -> Option<&Expression> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    match &unwrap_single_block_stmt(stmt).desc {
        StatementDesc::Return(expr) => Some(expr),
        _ => None,
    }
}

fn shared_return_guard_test(
    stmt: &Statement,
    fallback: &mut Option<Expression>,
) -> Option<Expression> {
    let StatementDesc::If(test, then_, else_) = &unwrap_single_block_stmt(stmt).desc else {
        return None;
    };
    if !else_.is_empty() {
        return None;
    }

    let then_return = single_wrapped_return_expr(then_)?;
    match fallback {
        Some(existing) if !ocaml_eq_expression(existing, then_return) => None,
        Some(_) => Some(test.clone()),
        None => {
            *fallback = Some(then_return.clone());
            Some(test.clone())
        }
    }
}

fn shared_return_guard_chain_terminal_success(
    stmt: &Statement,
    fallback: &mut Option<Expression>,
) -> Option<(Expression, Block)> {
    let StatementDesc::If(test, then_, else_) = &unwrap_single_block_stmt(stmt).desc else {
        return None;
    };

    let then_return = single_wrapped_return_expr(then_);
    let else_return = single_wrapped_return_expr(else_);

    let matches_fallback = |expr: &Expression, fallback: &Option<Expression>| match fallback {
        Some(existing) => ocaml_eq_expression(existing, expr),
        None => true,
    };

    if let Some(then_return) = then_return {
        if !else_.is_empty() && matches_fallback(then_return, fallback) {
            if fallback.is_none() {
                *fallback = Some(then_return.clone());
            }
            return Some((negate_tail_merge_condition(test), else_.clone()));
        }
    }

    if let Some(else_return) = else_return {
        if !then_.is_empty() && matches_fallback(else_return, fallback) {
            if fallback.is_none() {
                *fallback = Some(else_return.clone());
            }
            return Some((test.clone(), then_.clone()));
        }
    }

    None
}

fn decode_internal_utf8_string(s: &str) -> Cow<'_, str> {
    if s.is_ascii() {
        return Cow::Borrowed(s);
    }

    let mut bytes = Vec::with_capacity(s.len());
    for c in s.chars() {
        let code = c as u32;
        if code > 0xFF {
            return Cow::Borrowed(s);
        }
        bytes.push(code as u8);
    }

    match String::from_utf8(bytes) {
        Ok(decoded) => Cow::Owned(decoded),
        Err(_) => Cow::Borrowed(s),
    }
}

fn raw_snippet_exp_simple_enough(s: &str) -> bool {
    s.chars()
        .all(|c| matches!(c, 'a'..='z' | 'A'..='Z' | '_' | '.'))
}

fn raw_js_expression_needs_paren(code: &str) -> bool {
    match classify_js_exp(code) {
        JsExpClassification::JsLiteral { .. } => false,
        JsExpClassification::JsFunction { .. } | JsExpClassification::JsExpUnknown => {
            !raw_snippet_exp_simple_enough(code)
        }
    }
}

enum RawJsExpressionStatement {
    Omit,
    Comment(String),
    Normal,
}

fn classify_raw_js_expression_statement(expr: &Expression) -> RawJsExpressionStatement {
    match &expr.desc {
        ExpressionDesc::Var(_) | ExpressionDesc::Str { .. } => RawJsExpressionStatement::Omit,
        ExpressionDesc::RawJsCode(info) if info.is_stmt => {
            if matches!(
                classify_js_stmt(&info.code),
                JsStmtClassification::JsStmtComment
            ) {
                RawJsExpressionStatement::Comment(decode_internal_utf8_string(&info.code).into())
            } else {
                RawJsExpressionStatement::Normal
            }
        }
        ExpressionDesc::RawJsCode(info) => match classify_js_exp(&info.code) {
            JsExpClassification::JsLiteral {
                comment: Some(comment),
            } => RawJsExpressionStatement::Comment(comment),
            JsExpClassification::JsLiteral { comment: None } => RawJsExpressionStatement::Omit,
            JsExpClassification::JsFunction { .. } | JsExpClassification::JsExpUnknown => {
                RawJsExpressionStatement::Normal
            }
        },
        _ => RawJsExpressionStatement::Normal,
    }
}

fn expression_statement_prints_anything(expr: &Expression) -> bool {
    !matches!(
        classify_raw_js_expression_statement(expr),
        RawJsExpressionStatement::Omit
    )
}

fn member_target_needs_extra_group_indent(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Object(_, props) => props.len() > 1,
        ExpressionDesc::Array(elements, _) => elements.len() > 1,
        ExpressionDesc::OptionalBlock(inner, true) => member_target_needs_extra_group_indent(inner),
        _ => false,
    }
}

fn call_argument_needs_extra_group_indent(
    expr: &Expression,
    call_level: u8,
    current_indent: usize,
) -> bool {
    // OCaml's call printer adds an extra grouping level only when the call
    // itself is printed as a member/index target (`level == 15`). Preserve
    // that behavior, but suppress it in already-indented block contexts to
    // avoid double-indenting multiline literals.
    if call_level != 15 || current_indent != 0 {
        return false;
    }

    match &expr.desc {
        ExpressionDesc::Object(_, _) => true,
        ExpressionDesc::Array(elements, _) => elements.len() > 1,
        ExpressionDesc::OptionalBlock(inner, true) => {
            call_argument_needs_extra_group_indent(inner, call_level, current_indent)
        }
        _ => false,
    }
}

fn tag_info_has_untagged(attrs: &[crate::lambda::lam_tag_info::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.name == "unboxed")
}

fn tag_info_tag_name(attrs: &[crate::lambda::lam_tag_info::Attribute]) -> Option<&str> {
    attrs.iter().find_map(|attr| {
        if attr.name != "tag" {
            return None;
        }
        match &attr.payload {
            crate::lambda::lam_tag_info::AttributePayload::Str(value) => Some(value.as_str()),
            _ => None,
        }
    })
}

fn tag_info_runtime_tag(attrs: &[crate::lambda::lam_tag_info::Attribute]) -> Option<SwitchCaseTag> {
    attrs.iter().find_map(|attr| {
        if attr.name != "as" {
            return None;
        }
        match &attr.payload {
            crate::lambda::lam_tag_info::AttributePayload::Str(value) => {
                Some(SwitchCaseTag::String(value.clone()))
            }
            crate::lambda::lam_tag_info::AttributePayload::Int(value) => {
                Some(SwitchCaseTag::Int(*value))
            }
            crate::lambda::lam_tag_info::AttributePayload::Float(value) => {
                Some(SwitchCaseTag::Float(value.clone()))
            }
            crate::lambda::lam_tag_info::AttributePayload::BigInt(value) => {
                Some(SwitchCaseTag::BigInt(value.clone()))
            }
            crate::lambda::lam_tag_info::AttributePayload::Bool(value) => {
                Some(SwitchCaseTag::Bool(*value))
            }
            crate::lambda::lam_tag_info::AttributePayload::Ident(value) if value == "null" => {
                Some(SwitchCaseTag::Null)
            }
            crate::lambda::lam_tag_info::AttributePayload::Ident(value) if value == "undefined" => {
                Some(SwitchCaseTag::Undefined)
            }
            _ => None,
        }
    })
}

fn is_undefined_literal(expr: &Expression) -> bool {
    matches!(expr.desc, ExpressionDesc::Undefined { .. })
}

fn else_is_single_return_undefined(block: &Block) -> bool {
    return_is_undefined_block(block)
}

fn else_block_is_omitted_like_ocaml(block: &Block) -> bool {
    matches!(block.as_slice(), [])
        || matches!(
            block.as_slice(),
            [Statement {
                desc: StatementDesc::Block(inner),
                ..
            }] if inner.is_empty()
        )
        || matches!(
            block.as_slice(),
            [Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Var(_),
                    ..
                }),
                ..
            }]
        )
}

fn single_else_if_stmt_like_ocaml(block: &Block) -> Option<&Statement> {
    match block.as_slice() {
        [
            stmt @ Statement {
                desc: StatementDesc::If(_, _, _),
                ..
            },
        ] => Some(stmt),
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => match inner.as_slice() {
            [
                stmt @ Statement {
                    desc: StatementDesc::If(_, _, _),
                    ..
                },
            ] => Some(stmt),
            _ => None,
        },
        _ => None,
    }
}

fn return_is_undefined_block(block: &Block) -> bool {
    matches!(block.as_slice(), [stmt] if return_is_undefined(stmt))
}

fn return_is_undefined(stmt: &Statement) -> bool {
    matches!(
        stmt,
        Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Undefined { .. },
                ..
            }),
            ..
        }
    )
}

fn negate_tail_merge_condition(cond: &Expression) -> Expression {
    match &cond.desc {
        ExpressionDesc::Bool(value) => Expression::bool(!value),
        ExpressionDesc::JsNot(inner) => inner.as_ref().clone(),
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => Expression::bin(
            BinOp::NotEqEq,
            left.as_ref().clone(),
            right.as_ref().clone(),
        ),
        ExpressionDesc::Bin(BinOp::NotEqEq, left, right) => {
            Expression::bin(BinOp::EqEqEq, left.as_ref().clone(), right.as_ref().clone())
        }
        _ => Expression::not(cond.clone()),
    }
}

fn supported_single_negative_guard_condition(cond: &Expression) -> Option<Expression> {
    match &cond.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq | BinOp::NotEqEq, left, right)
            if single_negative_guard_subject_expr_supported(left)
                && single_negative_guard_tag_expr_supported(right) =>
        {
            Some(cond.clone())
        }
        ExpressionDesc::Bin(BinOp::EqEqEq | BinOp::NotEqEq, left, right)
            if single_negative_guard_subject_expr_supported(right)
                && single_negative_guard_tag_expr_supported(left) =>
        {
            Some(cond.clone())
        }
        _ => None,
    }
}

fn single_negative_guard_subject_expr_supported(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_) => true,
        ExpressionDesc::StaticIndex(target, _, _) => {
            single_negative_guard_subject_expr_supported(target)
        }
        _ => false,
    }
}

fn single_negative_guard_tag_expr_supported(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Str { .. } | ExpressionDesc::Var(_)
    )
}

fn supported_single_negative_guard_body(body: &Block) -> bool {
    body.iter()
        .all(|stmt| match &unwrap_single_block_stmt(stmt).desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Undefined { .. },
                ..
            }) => true,
            StatementDesc::Exp(expr) => supported_single_negative_guard_effect(expr),
            _ => false,
        })
}

fn supported_single_negative_guard_effect(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::Eq, left, _) => {
            supported_single_negative_guard_assign_target(left)
        }
        _ => false,
    }
}

fn supported_single_negative_guard_assign_target(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_) => true,
        ExpressionDesc::StaticIndex(target, _, _) | ExpressionDesc::ArrayIndex(target, _) => {
            single_negative_guard_subject_expr_supported(target)
        }
        _ => false,
    }
}

fn function_tail_statement_prints(stmt: &Statement) -> bool {
    !matches!(
        stmt.desc,
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Undefined { .. },
            ..
        })
    )
}

fn function_body_prints_any(stmts: &Block) -> bool {
    stmts.iter().enumerate().any(|(index, stmt)| {
        if index + 1 == stmts.len() {
            function_tail_statement_prints(stmt)
        } else {
            true
        }
    })
}

fn single_arrow_function_expr(body: &Block) -> Option<&Expression> {
    match body.as_slice() {
        [
            Statement {
                desc: StatementDesc::Return(expr),
                ..
            },
        ] if !matches!(expr.desc, ExpressionDesc::Undefined { .. }) => Some(expr),
        [
            Statement {
                desc: StatementDesc::Exp(expr),
                ..
            },
        ] => Some(expr),
        _ => None,
    }
}

fn format_char_comment(codepoint: i32) -> String {
    let escaped = match char::from_u32(codepoint as u32) {
        Some('\'') => "\\'".to_string(),
        Some('\\') => "\\\\".to_string(),
        Some('\n') => "\\n".to_string(),
        Some('\t') => "\\t".to_string(),
        Some('\r') => "\\r".to_string(),
        Some('\u{8}') => "\\b".to_string(),
        Some(c) => c.to_string(),
        None => "?".to_string(),
    };
    format!("'{escaped}'")
}

fn normalize_float_literal_for_js(float_str: &str) -> String {
    if is_hex_float_literal(float_str) {
        normalize_hex_float_literal(float_str).unwrap_or_else(|| transform_float_literal(float_str))
    } else {
        transform_float_literal(float_str)
    }
}

fn is_hex_float_literal(float_str: &str) -> bool {
    let bytes = float_str.as_bytes();
    let mut cur = 0;
    if matches!(bytes.first(), Some(b'-' | b'+')) {
        cur += 1;
    }
    matches!(bytes.get(cur), Some(b'0')) && matches!(bytes.get(cur + 1), Some(b'x' | b'X'))
}

fn normalize_hex_float_literal(float_str: &str) -> Option<String> {
    let value = parse_hex_float_literal(float_str)?;
    Some(js_number_to_string(value))
}

fn parse_hex_float_literal(float_str: &str) -> Option<f64> {
    let (negative, digits) = if let Some(rest) = float_str.strip_prefix('-') {
        (true, rest)
    } else if let Some(rest) = float_str.strip_prefix('+') {
        (false, rest)
    } else {
        (false, float_str)
    };

    let digits = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))?;
    let digits = digits.replace('_', "");
    if digits.is_empty() {
        return None;
    }

    let (mantissa, exponent) = if let Some((mantissa, exponent)) =
        digits.split_once('p').or_else(|| digits.split_once('P'))
    {
        (mantissa, exponent.parse::<i32>().ok()?)
    } else {
        (digits.as_str(), 0)
    };

    let (whole, fractional) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    if whole.is_empty() && fractional.is_empty() {
        return None;
    }

    let mut value = 0.0f64;
    for byte in whole.bytes().chain(fractional.bytes()) {
        value = value * 16.0 + hex_digit_value(byte)? as f64;
    }
    value *= 2.0f64.powi(exponent - (fractional.len() as i32 * 4));

    Some(if negative { -value } else { value })
}

fn hex_digit_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn js_number_to_string(value: f64) -> String {
    // OCaml converts every hexadecimal float through float_of_string and then
    // Js_number.to_string; see compiler/core/js_number.ml:42-57 and 93-97.
    if value == f64::INFINITY {
        "Infinity".to_string()
    } else if value == f64::NEG_INFINITY {
        "-Infinity".to_string()
    } else if value.is_nan() {
        "NaN".to_string()
    } else {
        let int_value = value as i64;
        if int_value as f64 == value {
            int_value.to_string()
        } else {
            value.to_string()
        }
    }
}

fn transform_float_literal(float_str: &str) -> String {
    let bytes = float_str.as_bytes();
    let len = bytes.len();
    let mut start = 0;
    while start + 1 < len && bytes[start] == b'0' && bytes[start + 1] != b'.' {
        start += 1;
    }

    let mut out = String::with_capacity(len.saturating_sub(start));
    for (idx, byte) in bytes[start..].iter().copied().enumerate() {
        if byte == b'_' {
            continue;
        }
        if byte == b'.' && start + idx == len - 1 {
            continue;
        }
        out.push(byte as char);
    }
    out
}

fn record_uses_array_syntax(fields: &[(String, bool)]) -> bool {
    !fields.is_empty()
        && fields
            .iter()
            .enumerate()
            .all(|(i, (field_name, _))| field_name == &i.to_string())
}

fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
        &name[2..name.len() - 1]
    } else {
        name
    }
}

pub(crate) fn convert_ident_name(name: &str) -> String {
    let name = unwrap_uppercase_exotic(name);
    if is_js_keyword_or_global(name) {
        format!("$${name}")
    } else {
        mangle_ident_name(name)
    }
}

fn mangle_ident_name(name: &str) -> String {
    if name
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '$'))
    {
        return name.to_string();
    }

    let mut out = String::with_capacity(name.len());
    for (idx, c) in name.chars().enumerate() {
        if c.is_ascii_alphanumeric() || matches!(c, '_' | '$') {
            out.push(c);
        } else {
            out.push_str(mangle_ident_char(c, idx == 0));
        }
    }
    out
}

fn mangle_ident_char(c: char, op: bool) -> &'static str {
    match c {
        '*' => "$star",
        '\'' => "$p",
        '!' => "$bang",
        '>' => "$great",
        '<' => "$less",
        '=' => "$eq",
        '+' => "$plus",
        '-' => {
            if op {
                "$neg"
            } else {
                "$"
            }
        }
        '@' => "$at",
        '^' => "$caret",
        '/' => "$slash",
        '|' => "$pipe",
        '.' => "$dot",
        '%' => "$percent",
        '~' => "$tilde",
        '#' => "$hash",
        ':' => "$colon",
        '?' => "$question",
        '&' => "$amp",
        '(' => "$lpar",
        ')' => "$rpar",
        '{' | '}' => "$lbrace",
        '[' => "$lbrack",
        ']' => "$rbrack",
        _ => "$unknown",
    }
}

fn printed_name_base_and_next_suffix(printed: &str) -> (String, usize) {
    match printed.rsplit_once('$') {
        Some((base, suffix)) if !base.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()) => {
            (base.to_string(), suffix.parse::<usize>().unwrap_or(0) + 1)
        }
        _ => (printed.to_string(), 1),
    }
}

#[derive(Default)]
struct JsIdentStats {
    defined_idents: HashSet<Ident>,
    used_idents: HashSet<Ident>,
}

impl JsIdentStats {
    fn with_defined(defined: impl IntoIterator<Item = Ident>) -> Self {
        let mut stats = Self::default();
        stats.defined_idents.extend(defined);
        stats
    }

    fn add_defined_ident(&mut self, ident: &Ident) {
        self.defined_idents.insert(ident.clone());
    }

    fn add_used_ident(&mut self, ident: &Ident) {
        if !self.defined_idents.contains(ident) {
            self.used_idents.insert(ident.clone());
        }
    }

    fn extend_free_idents(&mut self, other: HashSet<Ident>) {
        self.used_idents.extend(other);
    }

    fn free_variables(mut self) -> HashSet<Ident> {
        self.used_idents
            .retain(|ident| !self.defined_idents.contains(ident));
        self.used_idents
    }
}

fn free_variables_of_block_with_defined(
    block: &Block,
    defined: impl IntoIterator<Item = Ident>,
) -> HashSet<Ident> {
    let mut stats = JsIdentStats::with_defined(defined);
    collect_block_idents(block, &mut stats);
    stats.free_variables()
}

fn function_reserved_idents(
    params: &[Ident],
    body: &Block,
    function_ident: Option<&Ident>,
) -> Vec<Ident> {
    let mut reserved_idents: Vec<Ident> =
        free_variables_of_block_with_defined(body, params.iter().cloned())
            .into_iter()
            .collect();
    if let Some(function_ident) = function_ident {
        reserved_idents.push(function_ident.clone());
    }
    reserved_idents.sort();
    reserved_idents.dedup();
    reserved_idents
}

fn collect_block_idents(block: &Block, stats: &mut JsIdentStats) {
    for stmt in block {
        collect_statement_idents(stmt, stats);
    }
}

fn collect_statement_idents(stmt: &Statement, stats: &mut JsIdentStats) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_block_idents(block, stats),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            stats.add_defined_ident(ident);
            if let Some(value) = value {
                collect_expression_idents(value, stats);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_expression_idents(expr, stats);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(then_block, stats);
            collect_block_idents(else_block, stats);
        }
        StatementDesc::While(_, cond, body) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(body, stats);
        }
        StatementDesc::ForRange(_, start, finish, loop_ident, _, body) => {
            if let Some(start) = start {
                collect_expression_idents(start, stats);
            }
            collect_expression_idents(finish, stats);
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                std::iter::once(loop_ident.clone()),
            ));
        }
        StatementDesc::ForOf(_, loop_ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, loop_ident, iterable, body) => {
            collect_expression_idents(iterable, stats);
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                std::iter::once(loop_ident.clone()),
            ));
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for (_, clause) in clauses {
                collect_block_idents(&clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for clause in clauses {
                collect_block_idents(&clause.clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_block_idents(body, stats);
            if let Some((catch_ident, catch_block)) = catch {
                stats.extend_free_idents(free_variables_of_block_with_defined(
                    catch_block,
                    std::iter::once(catch_ident.clone()),
                ));
            }
            if let Some(finally) = finally {
                collect_block_idents(finally, stats);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn collect_expression_idents(expr: &Expression, stats: &mut JsIdentStats) {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => stats.add_used_ident(ident),
        ExpressionDesc::Var(VIdent::Qualified(module, _)) => stats.add_used_ident(&module.id),
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => collect_expression_idents(inner, stats),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_expression_idents(left, stats);
            collect_expression_idents(right, stats);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_expression_idents(test, stats);
            collect_expression_idents(consequent, stats);
            collect_expression_idents(alternate, stats);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_expression_idents(func, stats);
            for arg in args {
                collect_expression_idents(arg, stats);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_expression_idents(tag, stats);
            for string in strings {
                collect_expression_idents(string, stats);
            }
            for value in values {
                collect_expression_idents(value, stats);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => collect_expression_idents(target, stats),
        ExpressionDesc::New(target, args) => {
            collect_expression_idents(target, stats);
            if let Some(args) = args {
                for arg in args {
                    collect_expression_idents(arg, stats);
                }
            }
        }
        ExpressionDesc::Fun { params, body, .. } => {
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                params.iter().cloned(),
            ));
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
            collect_expression_idents(tag, stats);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_expression_idents(dup, stats);
            }
            for (_, value) in props {
                collect_expression_idents(value, stats);
            }
        }
    }
}

fn for_range_finish_needs_binding(expr: &Expression) -> bool {
    !matches!(
        expr.desc,
        ExpressionDesc::Number(_) | ExpressionDesc::Var(_)
    )
}

/// Get operator precedence (output_level, left_level, right_level)
fn op_precedence(op: BinOp) -> (u8, u8, u8) {
    match op {
        // Keep this table in lockstep with compiler/core/js_op_util.ml::op_prec.
        BinOp::Eq => (1, 13, 1),
        BinOp::Or => (3, 3, 3),
        BinOp::And => (4, 4, 4),
        BinOp::Bor => (5, 5, 5),
        BinOp::Bxor => (6, 6, 6),
        BinOp::Band => (7, 7, 7),
        BinOp::EqEqEq | BinOp::NotEqEq => (8, 8, 9),
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::InstanceOf => (9, 9, 10),
        BinOp::Lsl | BinOp::Lsr | BinOp::Asr => (10, 10, 11),
        BinOp::Plus | BinOp::Minus => (11, 11, 12),
        BinOp::Mul | BinOp::Div | BinOp::Mod => (12, 12, 13),
        BinOp::Pow => (13, 14, 12), // Right-associative
        BinOp::Bnot => (13, 13, 13),
    }
}

/// Check if a string is a valid JavaScript identifier
fn is_valid_js_ident(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' || c == '$' => {}
        _ => return false,
    }

    for c in chars {
        if !c.is_ascii_alphanumeric() && c != '_' && c != '$' {
            return false;
        }
    }

    !is_reserved_word(s)
}

fn property_access_uses_dot(s: &str) -> bool {
    let s = unwrap_uppercase_exotic(s);
    if s.is_empty() {
        return false;
    }

    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' || c == '$' => {}
        _ => return false,
    }

    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

/// Check if a string is a JavaScript reserved word
fn is_reserved_word(s: &str) -> bool {
    matches!(
        s,
        "break"
            | "case"
            | "catch"
            | "continue"
            | "debugger"
            | "default"
            | "delete"
            | "do"
            | "else"
            | "finally"
            | "for"
            | "function"
            | "if"
            | "in"
            | "instanceof"
            | "new"
            | "return"
            | "switch"
            | "this"
            | "throw"
            | "try"
            | "typeof"
            | "var"
            | "void"
            | "while"
            | "with"
            | "class"
            | "const"
            | "enum"
            | "export"
            | "extends"
            | "import"
            | "super"
            | "null"
            | "true"
            | "false"
    )
}

pub(crate) fn is_js_keyword_or_global(s: &str) -> bool {
    is_reserved_word(s)
        || matches!(
            s,
            "await"
                | "static"
                | "yield"
                | "implements"
                | "interface"
                | "package"
                | "private"
                | "protected"
                | "public"
                | "arguments"
                | "eval"
                | "AggregateError"
                | "Array"
                | "ArrayBuffer"
                | "AsyncFunction"
                | "AsyncGenerator"
                | "AsyncGeneratorFunction"
                | "AsyncIterator"
                | "Atomics"
                | "BigInt"
                | "BigInt64Array"
                | "BigUint64Array"
                | "Boolean"
                | "Bun"
                | "DataView"
                | "Date"
                | "decodeURI"
                | "decodeURIComponent"
                | "Deno"
                | "encodeURI"
                | "encodeURIComponent"
                | "Error"
                | "EvalError"
                | "FinalizationRegistry"
                | "Float16Array"
                | "Float32Array"
                | "Float64Array"
                | "Function"
                | "Generator"
                | "GeneratorFunction"
                | "globalThis"
                | "Infinity"
                | "Int16Array"
                | "Int32Array"
                | "Int8Array"
                | "Intl"
                | "isFinite"
                | "isNaN"
                | "Iterator"
                | "JSON"
                | "Map"
                | "Math"
                | "module"
                | "NaN"
                | "Number"
                | "Object"
                | "parseFloat"
                | "parseInt"
                | "Promise"
                | "Proxy"
                | "RangeError"
                | "ReferenceError"
                | "Reflect"
                | "RegExp"
                | "require"
                | "Set"
                | "SharedArrayBuffer"
                | "String"
                | "Symbol"
                | "SyntaxError"
                | "TypedArray"
                | "TypeError"
                | "Uint16Array"
                | "Uint32Array"
                | "Uint8Array"
                | "Uint8ClampedArray"
                | "undefined"
                | "URIError"
                | "WeakMap"
                | "WeakRef"
                | "WeakSet"
                | "__dirname"
                | "__filename"
                | "exports"
        )
}

/// Print an expression to a string
pub fn print_expression(expr: &Expression) -> String {
    let mut printer = JsPrinter::new();
    printer.print_expression(expr, 0);
    printer.into_output()
}

fn print_expression_with_level(expr: &Expression, level: u8) -> String {
    let mut printer = JsPrinter::new();
    printer.print_expression(expr, level);
    printer.into_output()
}

#[cfg(test)]
fn print_expression_with_debug(expr: &Expression, debug: bool) -> String {
    let mut printer = JsPrinter::with_module_path_resolver_and_debug(None, debug);
    printer.print_expression(expr, 0);
    printer.into_output()
}

#[cfg(test)]
fn print_expression_with_jsx_preserve(expr: &Expression, jsx_preserve: bool) -> String {
    let mut printer = JsPrinter::with_module_path_resolver_and_options(None, false, jsx_preserve);
    printer.print_expression(expr, 0);
    printer.into_output()
}

/// Print a block to a string
pub fn print_block(block: &Block) -> String {
    let mut printer = JsPrinter::new();
    printer.print_statements(block, true);
    printer.into_output()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::js_ir::op::{
        IdentInfo, ImportAttributes, LengthObject, MutableFlag, PropertyName, UsedStats,
    };
    use crate::js_ir::{CallInfo, Expression, ModuleId, ModulePathResolver, Statement};
    use crate::lambda::TagInfo;
    use std::path::Path;

    fn jsx_runtime_module() -> ModuleId {
        ModuleId {
            id: Ident::create_persistent("JsxRuntime"),
            kind: Kind::External {
                name: "react/jsx-runtime".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        }
    }

    #[test]
    fn test_print_bool() {
        let expr = Expression::bool(true);
        assert_eq!(print_expression(&expr), "true");

        let expr = Expression::bool(false);
        assert_eq!(print_expression(&expr), "false");
    }

    #[test]
    fn test_print_null_undefined() {
        let expr = Expression::null();
        assert_eq!(print_expression(&expr), "null");

        let expr = Expression::undefined(true);
        assert_eq!(print_expression(&expr), "undefined");
    }

    #[test]
    fn test_print_number() {
        let expr = Expression::number(Number::int(42));
        assert_eq!(print_expression(&expr), "42");

        let expr = Expression::number(Number::float("3.14"));
        assert_eq!(print_expression(&expr), "3.14");

        let expr = Expression::number(Number::float("1."));
        assert_eq!(print_expression(&expr), "1");

        let expr = Expression::number(Number::float("0012."));
        assert_eq!(print_expression(&expr), "12");

        let expr = Expression::number(Number::float("-0."));
        assert_eq!(print_expression(&expr), "-0");

        let expr = Expression::number(Number::float("0x10"));
        assert_eq!(print_expression(&expr), "16");

        let expr = Expression::number(Number::char('A'));
        assert_eq!(print_expression(&expr), "/* 'A' */65");

        let expr = Expression::number(Number::char('文'));
        assert_eq!(print_expression(&expr), "/* '文' */25991");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_for_range_finish_binding_suffix_persists_across_sibling_loops_like_ocaml() {
        let first = Statement::new(StatementDesc::ForRange(
            None,
            Some(Expression::number(Number::int(0))),
            Expression::call(
                Expression::var(Ident::create_local("finishExpr")),
                vec![Expression::number(Number::int(1))],
                CallInfo::default(),
            ),
            Ident::create_local("i"),
            ForDirection::Up,
            vec![],
        ));

        let second = Statement::new(StatementDesc::ForRange(
            None,
            Some(Expression::number(Number::int(0))),
            Expression::call(
                Expression::var(Ident::create_local("finishExpr")),
                vec![Expression::number(Number::int(2))],
                CallInfo::default(),
            ),
            Ident::create_local("i"),
            ForDirection::Up,
            vec![],
        ));

        let rendered = print_block(&vec![first, second]);

        assert!(rendered.contains("for (let i = 0, i_finish = finishExpr(1); i < i_finish; ++i)"));
        assert!(
            rendered
                .contains("for (let i$1 = 0, i_finish$1 = finishExpr(2); i$1 < i_finish$1; ++i$1)"),
            "expected sibling loop finish temp to keep the OCaml-style suffix, got:\n{rendered}"
        );
    }

    #[test]
    fn test_print_string() {
        let expr = Expression::string("hello");
        assert_eq!(print_expression(&expr), "\"hello\"");

        let expr = Expression::string("hello\nworld");
        assert_eq!(print_expression(&expr), "\"hello\\nworld\"");
    }

    #[test]
    fn test_print_string_decodes_internal_utf8_bytes_before_escaping() {
        let expr = Expression::string(latin1_encoded_utf8("\u{4f60}\u{597d}"));
        assert_eq!(print_expression(&expr), "\"\u{4f60}\u{597d}\"");
    }

    #[test]
    fn test_print_noquote_string_decodes_internal_utf8_bytes() {
        let regex = format!(
            "/Bucklescript{}/",
            "\u{662f}\u{4e00}\u{4e2a}\u{7a0b}\u{5e8f}\u{8bed}\u{8a00}"
        );
        let expr = Expression::new(ExpressionDesc::Str {
            txt: latin1_encoded_utf8(&regex),
            delim: Delim::NoQuotes,
        });
        assert_eq!(print_expression(&expr), regex);
    }

    #[test]
    fn test_print_tagged_template_decodes_internal_utf8_bytes() {
        let expr = Expression::new(ExpressionDesc::TaggedTemplate(
            Box::new(Expression::var(Ident::create_local("tag"))),
            vec![Expression::new(ExpressionDesc::Str {
                txt: latin1_encoded_utf8("\u{4f60}\u{597d}\u{ff0c}\n\u{4e16}\u{754c}"),
                delim: Delim::NoQuotes,
            })],
            vec![],
        ));

        assert_eq!(
            print_expression(&expr),
            format!("tag`\u{4f60}\u{597d}\u{ff0c}\n\u{4e16}\u{754c}`")
        );
    }

    #[test]
    fn test_print_array() {
        let expr = Expression::array(
            vec![
                Expression::number(Number::int(1)),
                Expression::number(Number::int(2)),
                Expression::number(Number::int(3)),
            ],
            MutableFlag::Immutable,
        );
        assert_eq!(print_expression(&expr), "[\n  1,\n  2,\n  3\n]");
    }

    #[test]
    fn test_print_singleton_array_preserves_nested_object_indentation_like_ocaml() {
        let expr = Expression::array(
            vec![Expression::new(ExpressionDesc::Object(
                None,
                vec![(PropertyName::lit("foo"), Expression::number(Number::int(1)))],
            ))],
            MutableFlag::Immutable,
        );

        assert_eq!(print_expression(&expr), "[{\n    foo: 1\n  }]");
    }

    #[test]
    fn test_print_binary() {
        let left = Expression::number(Number::int(1));
        let right = Expression::number(Number::int(2));
        let expr = Expression::bin(BinOp::Plus, left, right);
        assert_eq!(print_expression(&expr), "1 + 2");
    }

    #[test]
    fn test_print_shift_binary_is_parenthesized_like_ocaml() {
        let expr = Expression::bin(
            BinOp::Lsl,
            Expression::var(Ident::create_local("x")),
            Expression::number(Number::int(1)),
        );
        assert_eq!(print_expression(&expr), "(x << 1)");
    }

    #[test]
    fn test_print_chained_logical_and_without_right_nested_parens_like_ocaml() {
        let expr = Expression::bin(
            BinOp::And,
            Expression::var(Ident::create_local("a")),
            Expression::bin(
                BinOp::And,
                Expression::var(Ident::create_local("b")),
                Expression::var(Ident::create_local("c")),
            ),
        );
        assert_eq!(print_expression(&expr), "a && b && c");
    }

    #[test]
    fn test_print_chained_logical_or_without_right_nested_parens_like_ocaml() {
        let expr = Expression::bin(
            BinOp::Or,
            Expression::var(Ident::create_local("a")),
            Expression::bin(
                BinOp::Or,
                Expression::var(Ident::create_local("b")),
                Expression::var(Ident::create_local("c")),
            ),
        );
        assert_eq!(print_expression(&expr), "a || b || c");
    }

    #[test]
    fn test_print_nullish_or_as_loose_null_check_like_ocaml() {
        let value = Expression::var(Ident::create_local("x"));
        let expr = Expression::bin(
            BinOp::Or,
            Expression::bin(BinOp::EqEqEq, value.clone(), Expression::null()),
            Expression::bin(BinOp::EqEqEq, value.clone(), Expression::undefined(false)),
        );

        assert_eq!(print_expression(&expr), "x == null");
    }

    #[test]
    fn test_print_nullish_or_as_loose_null_check_in_reverse_order_like_ocaml() {
        let value = Expression::var(Ident::create_local("x"));
        let expr = Expression::bin(
            BinOp::Or,
            Expression::bin(BinOp::EqEqEq, value.clone(), Expression::undefined(false)),
            Expression::bin(BinOp::EqEqEq, value.clone(), Expression::null()),
        );

        assert_eq!(print_expression(&expr), "x == null");
    }

    #[test]
    fn test_print_chained_bitwise_or_without_right_nested_parens_like_ocaml() {
        let expr = Expression::bin(
            BinOp::Bor,
            Expression::var(Ident::create_local("a")),
            Expression::bin(
                BinOp::Bor,
                Expression::var(Ident::create_local("b")),
                Expression::var(Ident::create_local("c")),
            ),
        );
        assert_eq!(print_expression(&expr), "a | b | c");
    }

    #[test]
    fn test_print_zero_minus_expr_as_unary_minus() {
        let expr = Expression::bin(
            BinOp::Bor,
            Expression::bin(
                BinOp::Minus,
                Expression::number(Number::int(0)),
                Expression::var(Ident::create_local("x")),
            ),
            Expression::number(Number::int(0)),
        );
        assert_eq!(print_expression(&expr), "-x | 0");
    }

    #[test]
    fn test_print_zero_float_minus_expr_as_spaced_unary_minus() {
        let expr = Expression::bin(
            BinOp::Minus,
            Expression::number(Number::float("0.")),
            Expression::var(Ident::create_local("x")),
        );
        assert_eq!(print_expression(&expr), "- x");
    }

    #[test]
    fn test_print_typeof_function_parenthesizes_arrow_expression() {
        let value = Ident::create_local("value");
        let expr = Expression::new(ExpressionDesc::Typeof(Box::new(Expression::new(
            ExpressionDesc::Fun {
                is_method: false,
                params: vec![value.clone()],
                body: vec![Statement::return_(Expression::var(value))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            },
        ))));
        assert_eq!(print_expression(&expr), "typeof (value => value)");
    }

    #[test]
    fn test_print_typeof_simple_raw_js_omits_extra_parens() {
        let expr = Expression::new(ExpressionDesc::Typeof(Box::new(Expression::new(
            ExpressionDesc::RawJsCode(JsRawInfo {
                code: "__DEV__".to_string(),
                is_stmt: false,
            }),
        ))));
        assert_eq!(print_expression(&expr), "typeof __DEV__");
    }

    #[test]
    fn test_print_raw_js_regex_literal_omits_extra_parens() {
        let expr = Expression::new(ExpressionDesc::RawJsCode(JsRawInfo {
            code: "/foo/g".to_string(),
            is_stmt: false,
        }));
        assert_eq!(print_expression(&expr), "/foo/g");
    }

    #[test]
    fn test_print_raw_js_decodes_internal_utf8_bytes() {
        let expr = Expression::new(ExpressionDesc::RawJsCode(JsRawInfo {
            code: latin1_encoded_utf8(&format!(
                "/Bucklescript{}/",
                "\u{662f}\u{4e00}\u{4e2a}\u{7a0b}\u{5e8f}\u{8bed}\u{8a00}"
            )),
            is_stmt: false,
        }));
        assert_eq!(
            print_expression(&expr),
            format!(
                "/Bucklescript{}/",
                "\u{662f}\u{4e00}\u{4e2a}\u{7a0b}\u{5e8f}\u{8bed}\u{8a00}"
            )
        );
    }

    #[test]
    fn test_print_raw_js_function_expression_adds_parens() {
        let expr = Expression::new(ExpressionDesc::RawJsCode(JsRawInfo {
            code: "(a) => typeof a".to_string(),
            is_stmt: false,
        }));
        assert_eq!(print_expression(&expr), "((a) => typeof a)");
    }

    #[test]
    fn test_print_statement_calling_raw_js_function_expression_adds_statement_parens() {
        let expr = Expression::call(
            Expression::new(ExpressionDesc::RawJsCode(JsRawInfo {
                code: "(_)=> console.log('should works')".to_string(),
                is_stmt: false,
            })),
            vec![],
            CallInfo::default(),
        );
        let block = vec![Statement::exp(expr)];
        assert_eq!(
            print_block(&block),
            "(((_)=> console.log('should works'))());"
        );
    }

    #[test]
    fn test_print_parenthesized_object_statement_uses_ocaml_group_indent() {
        let stmt = Statement::exp(Expression::new(ExpressionDesc::Object(
            None,
            vec![
                (
                    PropertyName::lit("high"),
                    Expression::call(
                        Expression::var(Ident::create_local("add")),
                        vec![
                            Expression::number(Number::int(1)),
                            Expression::number(Number::int(2)),
                        ],
                        CallInfo::default(),
                    ),
                ),
                (PropertyName::lit("low"), Expression::number(Number::int(3))),
            ],
        )));

        assert_eq!(
            print_block(&vec![stmt]),
            "({\n    high: add(1, 2),\n    low: 3\n  });"
        );
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_block_preserves_raw_js_comment_literal_statements_like_ocaml() {
        let block = vec![
            Statement::exp(Expression::new(ExpressionDesc::RawJsCode(JsRawInfo {
                code: "//eslint-disable\n0".to_string(),
                is_stmt: false,
            }))),
            Statement::return_(Expression::var(Ident::create_local("x"))),
        ];

        assert_eq!(print_block(&block), "//eslint-disable\nreturn x;");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_block_preserves_comment_only_raw_js_statements_without_semicolon_like_ocaml() {
        let block = vec![
            Statement::exp(Expression::new(ExpressionDesc::RawJsCode(JsRawInfo {
                code: "/* comment */".to_string(),
                is_stmt: true,
            }))),
            Statement::return_(Expression::number(Number::int(1))),
        ];

        assert_eq!(print_block(&block), "/* comment */\nreturn 1;");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_conditional() {
        let cond = Expression::bool(true);
        let then_ = Expression::number(Number::int(1));
        let else_ = Expression::number(Number::int(2));
        let expr = Expression::cond(cond, then_, else_);
        assert_eq!(print_expression(&expr), "true ? 1 : 2");
    }

    #[test]
    fn test_print_parenthesized_conditional_uses_vertical_group() {
        let cond = Expression::var(Ident::create_local("x"));
        let then_ = Expression::number(Number::int(1));
        let else_ = Expression::number(Number::int(2));
        let expr = Expression::cond(cond, then_, else_);
        assert_eq!(print_expression_with_level(&expr, 3), "(\n  x ? 1 : 2\n)");
    }

    #[test]
    fn test_print_nested_conditional_else_branch_matches_ocaml_grouping() {
        let outer = Expression::cond(
            Expression::var(Ident::create_local("x")),
            Expression::number(Number::int(0)),
            Expression::cond(
                Expression::var(Ident::create_local("y")),
                Expression::number(Number::int(1)),
                Expression::number(Number::int(2)),
            ),
        );
        assert_eq!(print_expression(&outer), "x ? 0 : (\n    y ? 1 : 2\n  )");
    }

    #[test]
    fn test_print_call() {
        let id = Ident::create_local("foo");
        let func = Expression::var(id);
        let args = vec![Expression::number(Number::int(42))];
        let expr = Expression::call(func, args, CallInfo::default());
        assert!(print_expression(&expr).contains("(42)"));
    }

    #[test]
    fn test_print_call_omits_single_unit_undefined_argument() {
        let func = Expression::var(Ident::create_local("foo"));
        let expr = Expression::call(func, vec![Expression::undefined(true)], CallInfo::default());
        assert_eq!(print_expression(&expr), "foo()");
    }

    #[test]
    fn test_print_call_keeps_plain_undefined_argument() {
        let func = Expression::var(Ident::create_local("foo"));
        let expr = Expression::call(
            func,
            vec![Expression::undefined(false)],
            CallInfo::default(),
        );
        assert_eq!(print_expression(&expr), "foo(undefined)");
    }

    #[test]
    fn test_print_if_condition_call_object_argument_uses_snapshot_indent_like_ocaml() {
        let cond = Expression::bin(
            BinOp::NotEqEq,
            Expression::call(
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(Expression::var(Ident::create_local("Primitive_object"))),
                    "equal".to_string(),
                    None,
                )),
                vec![
                    Expression::var(Ident::create_local("e")),
                    Expression::new(ExpressionDesc::Object(
                        None,
                        vec![(
                            PropertyName::lit("RE_EXN_ID"),
                            Expression::var(Ident::create_local("Not_found")),
                        )],
                    )),
                ],
                CallInfo::default(),
            ),
            Expression::bool(false),
        );
        let stmt = Statement::new(StatementDesc::If(
            cond,
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![],
        ));

        assert_eq!(
            print_block(&vec![stmt]),
            "if (Primitive_object.equal(e, {\n    RE_EXN_ID: Not_found\n  }) !== false) {\n  return 1;\n}"
        );
    }

    #[test]
    fn test_print_transformed_jsx_component_call_uses_jsx_syntax() {
        let expr = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsx".to_string())),
            vec![
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(Expression::var(Ident::create_persistent("Foo"))),
                    "make".to_string(),
                    None,
                )),
                Expression::new(ExpressionDesc::Object(None, vec![])),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );

        assert_eq!(
            print_expression_with_jsx_preserve(&expr, true),
            "<Foo.make />"
        );
    }

    #[test]
    fn test_print_transformed_jsx_requires_jsx_preserve_flag_like_ocaml() {
        let expr = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsx".to_string())),
            vec![
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(Expression::var(Ident::create_persistent("Foo"))),
                    "make".to_string(),
                    None,
                )),
                Expression::new(ExpressionDesc::Object(None, vec![])),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );

        assert_eq!(print_expression(&expr), "JsxRuntime.jsx(Foo.make, {})");
    }

    #[test]
    fn test_print_transformed_jsx_children_keep_nested_jsx_unwrapped() {
        let strong = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsx".to_string())),
            vec![
                Expression::string("strong"),
                Expression::new(ExpressionDesc::Object(None, vec![])),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );
        let expr = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsxs".to_string())),
            vec![
                Expression::string("div"),
                Expression::new(ExpressionDesc::Object(
                    None,
                    vec![(
                        PropertyName::lit("children"),
                        Expression::array(
                            vec![strong, Expression::string("Hello, world!")],
                            MutableFlag::Immutable,
                        ),
                    )],
                )),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );

        assert_eq!(
            print_expression_with_jsx_preserve(&expr, true),
            "<div>\n  <strong />\n  {\"Hello, world!\"}\n</div>"
        );
    }

    #[test]
    fn test_print_transformed_jsx_record_block_props_like_ocaml() {
        let strong = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsx".to_string())),
            vec![
                Expression::string("strong"),
                Expression::new(ExpressionDesc::CamlBlock(
                    vec![],
                    MutableFlag::Immutable,
                    Box::new(Expression::number(Number::int(0))),
                    TagInfo::record(vec![], crate::parser::ast::MutableFlag::Immutable),
                )),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );
        let expr = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsxs".to_string())),
            vec![
                Expression::string("div"),
                Expression::new(ExpressionDesc::CamlBlock(
                    vec![
                        Expression::undefined(false),
                        Expression::array(
                            vec![strong, Expression::string("Hello, world!")],
                            MutableFlag::Immutable,
                        ),
                    ],
                    MutableFlag::Immutable,
                    Box::new(Expression::number(Number::int(0))),
                    TagInfo::record(
                        vec![
                            ("className".to_string(), true),
                            ("children".to_string(), false),
                        ],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                )),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );

        assert_eq!(
            print_expression_with_jsx_preserve(&expr, true),
            "<div>\n  <strong />\n  {\"Hello, world!\"}\n</div>"
        );
    }

    #[test]
    fn test_print_transformed_jsx_spread_and_key_props_like_ocaml() {
        let spread = Ident::create_persistent("newrecord");
        let expr = Expression::call(
            Expression::qualified(jsx_runtime_module(), Some("jsx".to_string())),
            vec![
                Expression::string("input"),
                Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(Expression::var(spread.clone())),
                            "type".to_string(),
                            None,
                        )),
                        Expression::string("text"),
                    )),
                    Box::new(Expression::var(spread.clone())),
                )),
                Expression::string("barry-key"),
            ],
            CallInfo {
                call_transformed_jsx: true,
                ..CallInfo::default()
            },
        );

        assert_eq!(
            print_expression_with_jsx_preserve(&expr, true),
            "<input\n  key={\"barry-key\"} \n  {...newrecord} \n  type={\"text\"}\n/>"
        );
    }

    #[test]
    fn test_print_new_member_constructor_omits_extra_parens_like_ocaml() {
        let expr = Expression::new(ExpressionDesc::New(
            Box::new(Expression::new(ExpressionDesc::StaticIndex(
                Box::new(Expression::qualified(
                    ModuleId {
                        id: Ident::create_local("React"),
                        kind: Kind::External {
                            name: "react".to_string(),
                            default: false,
                            import_attributes: None,
                        },
                        dynamic_import: false,
                    },
                    None,
                )),
                "Component".to_string(),
                None,
            ))),
            Some(vec![]),
        ));

        assert_eq!(print_expression(&expr), "new React.Component()");
    }

    #[test]
    fn test_print_new_global_member_constructor_keeps_parens_like_snapshot() {
        let expr = Expression::new(ExpressionDesc::New(
            Box::new(Expression::new(ExpressionDesc::StaticIndex(
                Box::new(Expression::var(Ident::create_local("global"))),
                "Buffer".to_string(),
                None,
            ))),
            Some(vec![Expression::number(Number::int(20))]),
        ));

        assert_eq!(print_expression(&expr), "new (global.Buffer)(20)");
    }

    #[test]
    fn test_print_optional_block_omits_unit_undefined_argument() {
        let expr = Expression::new(ExpressionDesc::OptionalBlock(
            Box::new(Expression::undefined(true)),
            false,
        ));
        assert_eq!(print_expression(&expr), "Primitive_option.some()");
    }

    #[test]
    fn test_print_optional_block_keeps_plain_undefined_argument() {
        let expr = Expression::new(ExpressionDesc::OptionalBlock(
            Box::new(Expression::undefined(false)),
            false,
        ));
        assert_eq!(print_expression(&expr), "Primitive_option.some(undefined)");
    }

    #[test]
    fn test_print_return() {
        let stmt = Statement::return_(Expression::number(Number::int(42)));
        let block = vec![stmt];
        assert_eq!(print_block(&block), "return 42;");
    }

    #[test]
    fn test_print_if() {
        let stmt = Statement::new(StatementDesc::If(
            Expression::bool(true),
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![Statement::return_(Expression::number(Number::int(2)))],
        ));
        let result = print_block(&vec![stmt]);
        assert!(result.contains("if (true)"));
        assert!(result.contains("return 1;"));
        assert!(result.contains("else"));
        assert!(result.contains("return 2;"));
    }

    #[test]
    fn test_print_if_omits_else_for_single_empty_block_like_ocaml() {
        let stmt = Statement::new(StatementDesc::If(
            Expression::bool(true),
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![Statement::new(StatementDesc::Block(vec![]))],
        ));

        assert_eq!(print_block(&vec![stmt]), "if (true) {\n  return 1;\n}");
    }

    #[test]
    fn test_print_if_omits_else_for_single_var_expression_like_ocaml() {
        let stmt = Statement::new(StatementDesc::If(
            Expression::bool(true),
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![Statement::exp(Expression::var(Ident::create_local(
                "ignored",
            )))],
        ));

        assert_eq!(print_block(&vec![stmt]), "if (true) {\n  return 1;\n}");
    }

    #[test]
    fn test_print_if_unwraps_single_block_else_if_like_ocaml() {
        let nested = Statement::new(StatementDesc::If(
            Expression::bool(false),
            vec![Statement::return_(Expression::number(Number::int(2)))],
            vec![],
        ));
        let stmt = Statement::new(StatementDesc::If(
            Expression::bool(true),
            vec![Statement::return_(Expression::number(Number::int(1)))],
            vec![Statement::new(StatementDesc::Block(vec![nested]))],
        ));

        assert_eq!(
            print_block(&vec![stmt]),
            "if (true) {\n  return 1;\n} else if (false) {\n  return 2;\n}"
        );
    }

    #[test]
    fn test_print_function_body_keeps_guard_return_fallthrough_tail_like_ocaml() {
        let state = Ident::create_local("state");
        let block = vec![
            Statement::new(StatementDesc::If(
                Expression::bin(
                    BinOp::NotEqEq,
                    Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                        state.clone(),
                    )))),
                    Expression::string("object".to_string()),
                ),
                vec![Statement::return_(Expression::number(Number::int(0)))],
                vec![],
            )),
            Statement::return_(Expression::bin(
                BinOp::Bor,
                Expression::bin(
                    BinOp::Plus,
                    Expression::number(Number::int(0)),
                    Expression::new(ExpressionDesc::StaticIndex(
                        Box::new(Expression::var(state)),
                        "_0".to_string(),
                        None,
                    )),
                ),
                Expression::number(Number::int(0)),
            )),
        ];

        let mut printer = JsPrinter::new();
        printer.print_function_body(&block, false);

        assert_eq!(
            printer.into_output(),
            "if (typeof state !== \"object\") {\n  return 0;\n}\nreturn 0 + state._0 | 0;"
        );
    }

    #[test]
    fn test_print_function_body_rewrites_strict_undefined_guard_return_suffix_into_positive_nested_guards()
     {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let block = vec![
            Statement::new(StatementDesc::If(
                Expression::bin(
                    BinOp::EqEqEq,
                    Expression::var(x.clone()),
                    Expression::undefined(false),
                ),
                vec![Statement::return_(Expression::bin(
                    BinOp::EqEqEq,
                    Expression::var(y.clone()),
                    Expression::undefined(false),
                ))],
                vec![],
            )),
            Statement::new(StatementDesc::If(
                Expression::bin(
                    BinOp::EqEqEq,
                    Expression::var(y.clone()),
                    Expression::undefined(false),
                ),
                vec![Statement::return_(Expression::bool(false))],
                vec![],
            )),
            Statement::return_(Expression::bin(
                BinOp::EqEqEq,
                Expression::var(x),
                Expression::var(y),
            )),
        ];

        let mut printer = JsPrinter::new();
        printer.print_function_body(&block, false);

        assert_eq!(
            printer.into_output(),
            "if (x !== undefined) {\n  if (y !== undefined) {\n    return x === y;\n  } else {\n    return false;\n  }\n} else {\n  return y === undefined;\n}"
        );
    }

    #[test]
    fn test_print_function_body_keeps_bound_success_tail_on_strict_undefined_guard() {
        let match_id = Ident::create_local("match");
        let tmp = Ident::create_local("tmp");
        let block = vec![
            Statement::new(StatementDesc::If(
                Expression::bin(
                    BinOp::EqEqEq,
                    Expression::var(match_id.clone()),
                    Expression::undefined(false),
                ),
                vec![Statement::return_(Expression::string("no"))],
                vec![],
            )),
            Statement::variable(VariableDeclaration {
                ident: tmp.clone(),
                value: Some(Expression::var(match_id)),
                property: crate::lambda::LetKind::Strict,
                ident_info: IdentInfo::default(),
            }),
            Statement::new(StatementDesc::If(
                Expression::bin(BinOp::EqEqEq, Expression::var(tmp), Expression::null()),
                vec![Statement::return_(Expression::string("yes"))],
                vec![],
            )),
            Statement::return_(Expression::string("no")),
        ];

        let mut printer = JsPrinter::new();
        printer.print_function_body(&block, false);
        let rendered = printer.into_output();

        assert!(rendered.starts_with("if (match === undefined) {"));
        assert!(rendered.contains("let tmp = match;"));
    }

    #[test]
    fn test_print_while() {
        let stmt = Statement::while_(Expression::bool(true), vec![Statement::break_()]);
        let result = print_block(&vec![stmt]);
        assert!(result.contains("while (true)"));
        assert!(result.contains("break;"));
    }

    #[test]
    fn test_print_empty_while_body_keeps_blank_line_like_ocaml() {
        let rendered = print_block(&vec![Statement::while_(Expression::bool(true), vec![])]);

        assert_eq!(rendered, "while (true) {\n  \n};");
    }

    #[test]
    fn test_print_if_keeps_blank_lines_for_hidden_branch_statements_like_ocaml() {
        let hidden = Statement::new(StatementDesc::Block(vec![Statement::exp(Expression::var(
            Ident::create_local("ignored"),
        ))]));
        let stmt = Statement::new(StatementDesc::If(
            Expression::bool(true),
            vec![
                Statement::exp(Expression::call(
                    Expression::var(Ident::create_local("log")),
                    vec![],
                    CallInfo::default(),
                )),
                hidden.clone(),
            ],
            vec![hidden],
        ));

        assert_eq!(
            print_block(&vec![stmt]),
            "if (true) {\n  log();\n  \n} else {\n  \n}"
        );
    }

    #[test]
    fn test_print_while_multiline_condition_keeps_hanging_indent_like_ocaml() {
        let cond = Expression::call(
            Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![],
                body: vec![
                    Statement::variable(VariableDeclaration {
                        ident: Ident::create_local("b"),
                        value: Some(Expression::number(Number::int(9))),
                        property: crate::lambda::lam_compat::LetKind::Strict,
                        ident_info: Default::default(),
                    }),
                    Statement::return_(Expression::bool(true)),
                ],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            }),
            vec![],
            CallInfo::default(),
        );
        let rendered = print_block(&vec![Statement::while_(cond, vec![Statement::break_()])]);

        assert_eq!(
            rendered,
            "while ((() => {\n    let b = 9;\n    return true;\n  })()) {\n  break;\n};"
        );
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_for_range_complex_finish_uses_finish_binding() {
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let finish = Expression::new(ExpressionDesc::Length(
            Box::new(Expression::var(xs)),
            LengthObject::Array,
        ));
        let stmt = Statement::new(StatementDesc::ForRange(
            None,
            Some(Expression::number(Number::int(0))),
            finish,
            i,
            ForDirection::Up,
            vec![],
        ));
        assert_eq!(
            print_block(&vec![stmt]),
            "for (let i = 0, i_finish = xs.length; i < i_finish; ++i) {}"
        );
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_for_range_without_init_binds_complex_finish_once() {
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let finish = Expression::new(ExpressionDesc::Length(
            Box::new(Expression::var(xs)),
            LengthObject::Array,
        ));
        let stmt = Statement::new(StatementDesc::ForRange(
            None,
            None,
            finish,
            i,
            ForDirection::Upto,
            vec![],
        ));
        assert_eq!(
            print_block(&vec![stmt]),
            "for (let i_finish = xs.length; i <= i_finish; ++i) {}"
        );
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_for_range_parenthesizes_sequence_init_in_header() {
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let side_effect = Ident::create_local("sideEffect");
        let init = Expression::new(ExpressionDesc::Seq(
            Box::new(Expression::call(
                Expression::var(side_effect),
                vec![],
                CallInfo::default(),
            )),
            Box::new(Expression::number(Number::int(0))),
        ));
        let finish = Expression::new(ExpressionDesc::Length(
            Box::new(Expression::var(xs)),
            LengthObject::Array,
        ));
        let stmt = Statement::new(StatementDesc::ForRange(
            None,
            Some(init),
            finish,
            i,
            ForDirection::Upto,
            vec![],
        ));
        assert_eq!(
            print_block(&vec![stmt]),
            "for (let i = (sideEffect(), 0), i_finish = xs.length; i <= i_finish; ++i) {}"
        );
    }

    #[test]
    fn test_print_block_preserves_top_level_function_order() {
        let before = Ident::create_local("before");
        let url = Ident::create_local("url");
        let after = Ident::create_local("after");
        let stmt_before = Statement::variable(VariableDeclaration {
            ident: before,
            value: Some(Expression::number(Number::int(1))),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        });
        let stmt_fun = Statement::variable(VariableDeclaration {
            ident: url.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![Ident::create_local("prim")],
                body: vec![Statement::return_(Expression::var(url))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        });
        let stmt_after = Statement::variable(VariableDeclaration {
            ident: after,
            value: Some(Expression::number(Number::int(2))),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        });

        let rendered = print_block(&vec![stmt_before, stmt_fun, stmt_after]);
        let before_idx = rendered.find("let before").unwrap();
        let fun_idx = rendered.find("function url").unwrap();
        let after_idx = rendered.find("let after").unwrap();
        assert!(before_idx < fun_idx);
        assert!(fun_idx < after_idx);
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_function_binding_reserves_own_name_inside_body_like_ocaml() {
        let function_ident = Ident::create_local("callback");
        let param = Ident::create_local("time");
        let inner = Ident::create_local("callback");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: function_ident,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![
                    Statement::variable(VariableDeclaration {
                        ident: inner.clone(),
                        value: Some(Expression::number(Number::int(1))),
                        property: crate::lambda::lam_compat::LetKind::Strict,
                        ident_info: Default::default(),
                    }),
                    Statement::return_(Expression::var(inner)),
                ],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("let callback = time => {"));
        assert!(rendered.contains("let callback$1 = 1;"));
        assert!(rendered.contains("return callback$1;"));
    }

    #[test]
    fn test_print_function_scope_allows_shadowing_uncaptured_outer_name() {
        let outer = Ident::create_local("x");
        let foo = Ident::create_local("foo");
        let param = Ident::create_local("x");
        let rendered = print_block(&vec![
            Statement::variable(VariableDeclaration {
                ident: outer,
                value: Some(Expression::number(Number::int(1))),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
            Statement::variable(VariableDeclaration {
                ident: foo,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![param.clone()],
                    body: vec![Statement::return_(Expression::var(param))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert!(rendered.contains("let x = 1;"));
        assert!(rendered.contains("function foo(x) {"));
        assert!(rendered.contains("return x;"));
        assert!(!rendered.contains("function foo(x$1) {"));
    }

    #[test]
    fn test_print_function_scope_preserves_captured_outer_name() {
        let outer = Ident::create_local("value");
        let foo = Ident::create_local("foo");
        let param = Ident::create_local("arg");
        let rendered = print_block(&vec![
            Statement::variable(VariableDeclaration {
                ident: outer.clone(),
                value: Some(Expression::number(Number::int(1))),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
            Statement::variable(VariableDeclaration {
                ident: foo,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![param.clone()],
                    body: vec![Statement::return_(Expression::bin(
                        BinOp::Plus,
                        Expression::var(outer),
                        Expression::var(param),
                    ))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert!(rendered.contains("function foo(arg) {"));
        assert!(rendered.contains("return value + arg;"));
    }

    #[test]
    fn test_print_function_scope_copies_captured_base_suffix_map_like_ocaml() {
        let outer_start = Ident::create_local("match");
        let outer_end = Ident::create_local("match");
        let callback = Ident::create_local("callback");
        let param = Ident::create_local("preset");
        let inner_match = Ident::create_local("match");

        let rendered = print_block(&vec![
            Statement::variable(VariableDeclaration {
                ident: outer_start.clone(),
                value: Some(Expression::number(Number::int(1))),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
            Statement::variable(VariableDeclaration {
                ident: outer_end,
                value: Some(Expression::number(Number::int(2))),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
            Statement::variable(VariableDeclaration {
                ident: callback,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![param],
                    body: vec![
                        Statement::variable(VariableDeclaration {
                            ident: inner_match.clone(),
                            value: Some(Expression::number(Number::int(3))),
                            property: crate::lambda::lam_compat::LetKind::Strict,
                            ident_info: Default::default(),
                        }),
                        Statement::return_(Expression::bin(
                            BinOp::Plus,
                            Expression::var(outer_start),
                            Expression::var(inner_match),
                        )),
                    ],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert!(rendered.contains("let match = 1;"));
        assert!(rendered.contains("let match$1 = 2;"));
        assert!(rendered.contains("let match$2 = 3;"));
        assert!(rendered.contains("return match + match$2;"));
    }

    #[test]
    fn test_print_unit_function_elides_tail_return_statement() {
        let foo = Ident::create_local("remove");
        let param = Ident::create_local("id");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: foo,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param.clone()],
                body: vec![Statement::return_(Expression::call(
                    Expression::qualified(
                        ModuleId {
                            id: Ident::create_local("Belt_MutableMapInt"),
                            kind: Kind::Ml,
                            dynamic_import: false,
                        },
                        Some("remove".to_string()),
                    ),
                    vec![
                        Expression::var(Ident::create_local("mockMap")),
                        Expression::var(param),
                    ],
                    CallInfo::default(),
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("function remove(id) {"));
        assert!(rendered.contains("Belt_MutableMapInt.remove(mockMap, id);"));
        assert!(!rendered.contains("return Belt_MutableMapInt.remove"));
    }

    #[test]
    fn test_print_unit_arrow_function_elides_tail_return_statement() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: vec![Statement::return_(Expression::call(
                Expression::qualified(
                    ModuleId {
                        id: Ident::create_local("Test_utils"),
                        kind: Kind::Ml,
                        dynamic_import: false,
                    },
                    Some("eq".to_string()),
                ),
                vec![
                    Expression::string("loc"),
                    Expression::number(Number::int(1)),
                    Expression::number(Number::int(1)),
                ],
                CallInfo::default(),
            ))],
            env: Default::default(),
            return_unit: true,
            async_: false,
            directive: None,
        }));

        assert_eq!(rendered, "() => Test_utils.eq(\"loc\", 1, 1)");
    }

    #[test]
    fn test_print_arrow_function_with_undefined_body_uses_compact_empty_block() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: vec![Statement::return_(Expression::undefined(false))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }));

        assert_eq!(rendered, "() => {}");
    }

    #[test]
    fn test_print_named_function_with_undefined_body_keeps_blank_line_like_ocaml() {
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: Ident::create_local("n"),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![Ident::create_local("prim")],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert_eq!(rendered, "function n(prim) {\n  \n}");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_arrow_function_parenthesizes_object_literal_body() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: vec![Statement::return_(Expression::new(ExpressionDesc::Object(
                None,
                vec![(
                    PropertyName::lit("default"),
                    Expression::number(Number::int(1)),
                )],
            )))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }));

        assert_eq!(rendered, "() => ({\n  \"default\": 1\n})");
    }

    #[test]
    fn test_print_arrow_function_parenthesizes_constructor_block_body() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: vec![Statement::return_(Expression::new(
                ExpressionDesc::CamlBlock(
                    vec![Expression::number(Number::int(1))],
                    MutableFlag::Immutable,
                    Box::new(Expression::number(Number::int(0))),
                    TagInfo::constructor("Some", 1, 0),
                ),
            ))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }));

        assert_eq!(rendered, "() => ({\n  TAG: \"Some\",\n  _0: 1\n})");
    }

    #[test]
    fn test_print_arrow_function_preserves_parenthesized_shift_body() {
        let value = Ident::create_local("value");
        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![value.clone()],
            body: vec![Statement::return_(Expression::bin(
                BinOp::Lsl,
                Expression::var(value),
                Expression::number(Number::int(1)),
            ))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }));

        assert_eq!(rendered, "value => (value << 1)");
    }

    #[test]
    fn test_print_unit_function_tail_if_drops_else_return_undefined() {
        let foo = Ident::create_local("foo");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: foo,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![],
                body: vec![Statement::new(StatementDesc::If(
                    Expression::var(Ident::create_local("cond")),
                    vec![Statement::exp(Expression::call(
                        Expression::qualified(
                            ModuleId {
                                id: Ident::create_local("console"),
                                kind: Kind::Ml,
                                dynamic_import: false,
                            },
                            Some("log".to_string()),
                        ),
                        vec![Expression::string("hit")],
                        CallInfo::default(),
                    ))],
                    vec![Statement::return_(Expression::undefined(true))],
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (cond) {"));
        assert!(rendered.contains("console.log(\"hit\");"));
        assert!(!rendered.contains("else"));
        assert!(!rendered.contains("return;"));
    }

    #[test]
    fn test_print_unit_function_tail_nested_if_merges_conditions_like_ocaml() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_is_space = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    key_is_space,
                    vec![Statement::new(StatementDesc::If(
                        state_active,
                        vec![
                            Statement::exp(Expression::call(
                                Expression::var(do_action),
                                vec![Expression::var(state)],
                                CallInfo::default(),
                            )),
                            Statement::return_(Expression::undefined(true)),
                        ],
                        vec![Statement::return_(Expression::undefined(true))],
                    ))],
                    vec![],
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("if (state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    fn test_print_unit_function_tail_block_wrapped_nested_if_merges_conditions_like_ocaml() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_is_space = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![Statement::new(StatementDesc::Block(vec![Statement::new(
                    StatementDesc::If(
                        key_is_space,
                        vec![Statement::new(StatementDesc::If(
                            state_active,
                            vec![
                                Statement::exp(Expression::call(
                                    Expression::var(do_action),
                                    vec![Expression::var(state)],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![Statement::return_(Expression::undefined(true))],
                        ))],
                        vec![],
                    ),
                )]))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("if (state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    fn test_print_unit_function_body_with_trailing_return_merges_nested_if_like_ocaml() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_is_space = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        key_is_space,
                        vec![Statement::new(StatementDesc::If(
                            state_active,
                            vec![
                                Statement::exp(Expression::call(
                                    Expression::var(do_action),
                                    vec![Expression::var(state)],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![Statement::return_(Expression::undefined(true))],
                        ))],
                        vec![],
                    )),
                    Statement::return_(Expression::undefined(true)),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("if (state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_unit_function_body_with_large_literal_dispatch_merges_to_exact_literal_like_ocaml()
     {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_is_space = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let rest = [
            "q", "p", "o", "n", "m", "l", "k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a",
        ]
        .into_iter()
        .map(|txt| {
            Expression::bin(
                BinOp::EqEqEq,
                Expression::var(key.clone()),
                Expression::string(txt),
            )
        })
        .reduce(|acc, expr| Expression::bin(BinOp::Or, acc, expr))
        .expect("expected a non-empty literal chain");
        let dispatch = Expression::bin(BinOp::Or, key_is_space.clone(), rest);
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        dispatch,
                        vec![Statement::new(StatementDesc::If(
                            key_is_space,
                            vec![Statement::new(StatementDesc::If(
                                state_active,
                                vec![
                                    Statement::exp(Expression::call(
                                        Expression::var(do_action),
                                        vec![Expression::var(state)],
                                        CallInfo::default(),
                                    )),
                                    Statement::return_(Expression::undefined(true)),
                                ],
                                vec![Statement::return_(Expression::undefined(true))],
                            ))],
                            vec![],
                        ))],
                        vec![],
                    )),
                    Statement::return_(Expression::undefined(true)),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("key === \"q\""));
        assert!(!rendered.contains("if (key === \"space\" ||"));
        assert!(!rendered.contains("if (key === \"space\")"));
        assert!(!rendered.contains("if (state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_unit_function_body_collapses_nested_negative_guard_chain_like_ocaml() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_not_space = Expression::bin(
            BinOp::NotEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let rest = [
            "q", "p", "o", "n", "m", "l", "k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a",
        ]
        .into_iter()
        .map(|txt| {
            Expression::bin(
                BinOp::NotEqEq,
                Expression::var(key.clone()),
                Expression::string(txt),
            )
        })
        .reduce(|acc, expr| Expression::bin(BinOp::And, acc, expr))
        .expect("expected a non-empty literal chain");
        let dispatch = Expression::bin(BinOp::And, key_not_space.clone(), rest);
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![Statement::new(StatementDesc::Block(vec![
                    Statement::new(StatementDesc::If(
                        dispatch,
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::new(StatementDesc::Block(vec![
                        Statement::new(StatementDesc::If(
                            key_not_space,
                            vec![Statement::return_(Expression::undefined(true))],
                            vec![],
                        )),
                        Statement::new(StatementDesc::Block(vec![
                            Statement::new(StatementDesc::If(
                                Expression::not(state_active.clone()),
                                vec![Statement::return_(Expression::undefined(true))],
                                vec![],
                            )),
                            Statement::exp(Expression::call(
                                Expression::var(do_action),
                                vec![Expression::var(state)],
                                CallInfo::default(),
                            )),
                            Statement::return_(Expression::undefined(true)),
                        ])),
                    ])),
                ]))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("key !== \"q\""));
        assert!(!rendered.contains("if (key !== \"space\")"));
        assert!(!rendered.contains("if (!state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_unit_function_body_collapses_flat_negative_guard_chain_like_ocaml() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_not_space = Expression::bin(
            BinOp::NotEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let rest = [
            "q", "p", "o", "n", "m", "l", "k", "j", "i", "h", "g", "f", "e", "d", "c", "b", "a",
        ]
        .into_iter()
        .map(|txt| {
            Expression::bin(
                BinOp::NotEqEq,
                Expression::var(key.clone()),
                Expression::string(txt),
            )
        })
        .reduce(|acc, expr| Expression::bin(BinOp::And, acc, expr))
        .expect("expected a non-empty literal chain");
        let dispatch = Expression::bin(BinOp::And, key_not_space.clone(), rest);
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        dispatch,
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::new(StatementDesc::If(
                        key_not_space,
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::new(StatementDesc::If(
                        Expression::not(state_active.clone()),
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::exp(Expression::call(
                        Expression::var(do_action),
                        vec![Expression::var(state)],
                        CallInfo::default(),
                    )),
                    Statement::return_(Expression::undefined(true)),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("key !== \"q\""));
        assert!(!rendered.contains("if (key !== \"space\")"));
        assert!(!rendered.contains("if (!state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    fn test_print_non_unit_function_body_collapses_shared_return_guard_chain_like_ocaml() {
        let check = Ident::create_local("check");
        let match_ = Ident::create_local("match");
        let value = Ident::create_local("value");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: check,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![match_.clone(), value.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::EqEqEq,
                            Expression::var(match_.clone()),
                            Expression::undefined(true),
                        ),
                        vec![Statement::return_(Expression::string("fallback"))],
                        vec![],
                    )),
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::var(value.clone()),
                            Expression::undefined(true),
                        ),
                        vec![Statement::return_(Expression::string("fallback"))],
                        vec![Statement::return_(Expression::string("success"))],
                    )),
                ],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (match !== undefined && value === undefined) {"),
            "{rendered}"
        );
        assert!(rendered.contains("return \"success\";"), "{rendered}");
        assert!(rendered.contains("return \"fallback\";"), "{rendered}");
        assert!(
            !rendered.contains("if (match === undefined) {"),
            "{rendered}"
        );
        assert!(
            !rendered.contains("if (value !== undefined) {"),
            "{rendered}"
        );
    }

    #[test]
    fn test_print_non_unit_function_body_collapses_shared_success_else_if_chain_like_ocaml() {
        let show = Ident::create_local("show");
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let c = Ident::create_local("c");
        let result = Ident::create_local("result");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: show,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![a.clone(), b.clone(), c.clone(), result.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    Expression::bin(
                        BinOp::NotEqEq,
                        Expression::var(a.clone()),
                        Expression::number(Number::int(0)),
                    ),
                    vec![Statement::return_(Expression::var(result.clone()))],
                    vec![Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::var(b.clone()),
                            Expression::number(Number::int(0)),
                        ),
                        vec![Statement::return_(Expression::var(result.clone()))],
                        vec![Statement::new(StatementDesc::If(
                            Expression::bin(
                                BinOp::NotEqEq,
                                Expression::var(c.clone()),
                                Expression::number(Number::int(0)),
                            ),
                            vec![Statement::return_(Expression::var(result.clone()))],
                            vec![Statement::return_(Expression::string("zeroes"))],
                        ))],
                    ))],
                ))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (a === 0 && b === 0 && c === 0) {"),
            "{rendered}"
        );
        assert!(rendered.contains("return \"zeroes\";"), "{rendered}");
        assert!(rendered.contains("return result;"), "{rendered}");
        assert!(!rendered.contains("if (a !== 0) {"), "{rendered}");
        assert!(!rendered.contains("else if (b !== 0) {"), "{rendered}");
        assert!(!rendered.contains("else if (c !== 0) {"), "{rendered}");
    }

    #[test]
    fn test_print_non_unit_function_body_inverts_shared_success_or_guard_into_fallthrough() {
        let show = Ident::create_local("show");
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let c = Ident::create_local("c");
        let result = Ident::create_local("result");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: show,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![a.clone(), b.clone(), c.clone(), result.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    Expression::bin(
                        BinOp::Or,
                        Expression::bin(
                            BinOp::Or,
                            Expression::bin(
                                BinOp::NotEqEq,
                                Expression::var(a.clone()),
                                Expression::number(Number::int(0)),
                            ),
                            Expression::bin(
                                BinOp::NotEqEq,
                                Expression::var(b.clone()),
                                Expression::number(Number::int(0)),
                            ),
                        ),
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::var(c.clone()),
                            Expression::number(Number::int(0)),
                        ),
                    ),
                    vec![Statement::return_(Expression::var(result.clone()))],
                    vec![Statement::return_(Expression::string("zeroes"))],
                ))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (a === 0 && b === 0 && c === 0) {"),
            "{rendered}"
        );
        assert!(rendered.contains("return \"zeroes\";"), "{rendered}");
        assert!(rendered.contains("return result;"), "{rendered}");
        assert!(
            !rendered.contains("if (a !== 0 || b !== 0 || c !== 0) {"),
            "{rendered}"
        );
        assert!(!rendered.contains("} else {"), "{rendered}");
    }

    #[test]
    fn test_print_non_unit_function_body_drops_dead_undefined_binding_before_throw_guard() {
        let assert_f = Ident::create_local("assert_f");
        let x = Ident::create_local("x");
        let match_ = Ident::create_local("match");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: assert_f,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![x.clone()],
                body: vec![
                    Statement::variable(VariableDeclaration {
                        ident: match_.clone(),
                        value: None,
                        property: crate::lambda::lam_compat::LetKind::Strict,
                        ident_info: Default::default(),
                    }),
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::Gt,
                            Expression::var(x.clone()),
                            Expression::number(Number::int(3)),
                        ),
                        vec![Statement::exp(Expression::bin(
                            BinOp::Eq,
                            Expression::var(match_),
                            Expression::undefined(true),
                        ))],
                        vec![Statement::throw(Expression::string("boom"))],
                    )),
                    Statement::return_(Expression::number(Number::int(3))),
                ],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (x <= 3) {"), "{rendered}");
        assert!(rendered.contains("throw \"boom\";"), "{rendered}");
        assert!(rendered.contains("return 3;"), "{rendered}");
        assert!(!rendered.contains("let match;"), "{rendered}");
        assert!(!rendered.contains("match = undefined;"), "{rendered}");
        assert!(!rendered.contains("if (x > 3) {"), "{rendered}");
        assert!(!rendered.contains("} else {"), "{rendered}");
    }

    #[test]
    fn test_print_non_unit_function_body_drops_dead_undefined_binding_before_throw_guard_when_wrapped()
     {
        let assert_f = Ident::create_local("assert_f");
        let x = Ident::create_local("x");
        let match_ = Ident::create_local("match");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: assert_f,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![x.clone()],
                body: vec![Statement::new(StatementDesc::Block(vec![
                    Statement::variable(VariableDeclaration {
                        ident: match_.clone(),
                        value: None,
                        property: crate::lambda::lam_compat::LetKind::Strict,
                        ident_info: Default::default(),
                    }),
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::Gt,
                            Expression::var(x.clone()),
                            Expression::number(Number::int(3)),
                        ),
                        vec![Statement::exp(Expression::bin(
                            BinOp::Eq,
                            Expression::var(match_),
                            Expression::undefined(true),
                        ))],
                        vec![Statement::throw(Expression::string("boom"))],
                    )),
                    Statement::return_(Expression::number(Number::int(3))),
                ]))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (x <= 3) {"), "{rendered}");
        assert!(rendered.contains("throw \"boom\";"), "{rendered}");
        assert!(rendered.contains("return 3;"), "{rendered}");
        assert!(!rendered.contains("let match;"), "{rendered}");
        assert!(!rendered.contains("match = undefined;"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_keeps_single_negative_guard_like_ocaml() {
        let handle = Ident::create_local("handle");
        let q = Ident::create_local("q");
        let do_action = Ident::create_local("doAction");
        let q_length = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(q.clone())),
            "length".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![q],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(BinOp::Le, q_length, Expression::number(Number::int(0))),
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::exp(Expression::call(
                        Expression::var(do_action),
                        vec![],
                        CallInfo::default(),
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (q.length <= 0) {"));
        assert!(rendered.contains("doAction();"));
        assert!(!rendered.contains("if (q.length > 0) {"));
    }

    #[test]
    fn test_print_unit_function_body_flips_single_clean_negative_guard_like_ocaml() {
        let handle = Ident::create_local("handle");
        let value = Ident::create_local("value");
        let state = Ident::create_local("state");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![value.clone(), state.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::var(value.clone()),
                            Expression::string("b"),
                        ),
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(Expression::var(state)),
                            "contents".to_string(),
                            None,
                        )),
                        Expression::string("b"),
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (value === \"b\") {"), "{rendered}");
        assert!(rendered.contains("state.contents = \"b\";"), "{rendered}");
        assert!(rendered.contains("return;"), "{rendered}");
        assert!(!rendered.contains("if (value !== \"b\") {"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_keeps_single_negative_guard_before_loop_like_ocaml() {
        let handle = Ident::create_local("handle");
        let len = Ident::create_local("len");
        let k = Ident::create_local("k");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![len.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::EqEqEq,
                            Expression::var(len.clone()),
                            Expression::number(Number::int(0)),
                        ),
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::new(StatementDesc::ForRange(
                        None,
                        Some(Expression::number(Number::int(0))),
                        Expression::number(Number::int(1)),
                        k,
                        ForDirection::Up,
                        vec![],
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (len === 0) {"), "{rendered}");
        assert!(
            rendered.contains("for (let k = 0; k < 1; ++k) {"),
            "{rendered}"
        );
        assert!(!rendered.contains("if (len !== 0) {"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_keeps_single_negative_guard_before_call_like_ocaml() {
        let handle = Ident::create_local("handle");
        let obj = Ident::create_local("obj");
        let size = Ident::create_local("size");
        let log = Ident::create_local("log");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![obj.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::EqEqEq,
                            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                                obj.clone(),
                            )))),
                            Expression::string("function"),
                        ),
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![],
                    )),
                    Statement::variable(VariableDeclaration {
                        ident: size,
                        value: Some(Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(Expression::var(obj)),
                            "length".to_string(),
                            None,
                        ))),
                        property: crate::lambda::lam_compat::LetKind::Strict,
                        ident_info: Default::default(),
                    }),
                    Statement::exp(Expression::call(
                        Expression::var(log),
                        vec![],
                        CallInfo::default(),
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (typeof obj === \"function\") {"),
            "{rendered}"
        );
        assert!(rendered.contains("let size = obj.length;"), "{rendered}");
        assert!(rendered.contains("log();"), "{rendered}");
        assert!(
            !rendered.contains("if (typeof obj !== \"function\") {"),
            "{rendered}"
        );
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_unit_function_body_with_trailing_return_merges_nested_if_without_inner_else() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_is_space = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        key_is_space,
                        vec![Statement::new(StatementDesc::If(
                            state_active,
                            vec![
                                Statement::exp(Expression::call(
                                    Expression::var(do_action),
                                    vec![Expression::var(state)],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![],
                        ))],
                        vec![],
                    )),
                    Statement::return_(Expression::undefined(true)),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("if (state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    fn test_print_unit_function_tail_merges_nested_if_when_outer_else_is_return_undefined() {
        let handle_key = Ident::create_local("handleKey");
        let state = Ident::create_local("state");
        let key = Ident::create_local("key");
        let do_action = Ident::create_local("doAction");
        let key_is_space = Expression::bin(
            BinOp::EqEqEq,
            Expression::var(key.clone()),
            Expression::string("space"),
        );
        let state_active = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(state.clone())),
            "active".to_string(),
            None,
        ));
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle_key,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![state.clone(), key.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    key_is_space,
                    vec![Statement::new(StatementDesc::If(
                        state_active,
                        vec![
                            Statement::exp(Expression::call(
                                Expression::var(do_action),
                                vec![Expression::var(state)],
                                CallInfo::default(),
                            )),
                            Statement::return_(Expression::undefined(true)),
                        ],
                        vec![Statement::return_(Expression::undefined(true))],
                    ))],
                    vec![Statement::return_(Expression::undefined(true))],
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (key === \"space\" && state.active) {"));
        assert!(rendered.contains("doAction(state);"));
        assert!(rendered.contains("return;"));
        assert!(!rendered.contains("if (state.active)"));
        assert!(!rendered.contains("else"));
    }

    #[test]
    fn test_print_unit_function_tail_merges_nested_negative_guard_with_implicit_outer_return() {
        let foo4 = Ident::create_local("foo4");
        let x = Ident::create_local("x");
        let h = Ident::create_local("h");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: foo4,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![x.clone(), h.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    Expression::bin(
                        BinOp::And,
                        Expression::bin(
                            BinOp::EqEqEq,
                            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                                x.clone(),
                            )))),
                            Expression::string("object"),
                        ),
                        Expression::bin(
                            BinOp::EqEqEq,
                            Expression::new(ExpressionDesc::StaticIndex(
                                Box::new(Expression::var(x.clone())),
                                "NAME".to_string(),
                                None,
                            )),
                            Expression::string("Foo"),
                        ),
                    ),
                    vec![Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::new(ExpressionDesc::StaticIndex(
                                Box::new(Expression::var(x.clone())),
                                "VAL".to_string(),
                                None,
                            )),
                            Expression::number(Number::int(3)),
                        ),
                        vec![Statement::return_(Expression::undefined(true))],
                        vec![Statement::return_(Expression::call(
                            Expression::var(h),
                            vec![],
                            CallInfo::default(),
                        ))],
                    ))],
                    vec![],
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered
                .contains("if (typeof x === \"object\" && x.NAME === \"Foo\" && x.VAL === 3) {"),
            "{rendered}"
        );
        assert!(rendered.contains("return h();"), "{rendered}");
        assert!(!rendered.contains("if (x.VAL !== 3)"), "{rendered}");
        assert!(!rendered.contains("} else {"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_merges_shared_tail_into_nested_if_else() {
        let do_with_b = Ident::create_local("doWithB");
        let console_log = Expression::qualified(
            ModuleId {
                id: Ident::create_local("console"),
                kind: Kind::External {
                    name: "console".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            Some("log".to_string()),
        );
        let b = Ident::create_local("b");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: do_with_b,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![b.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                                b.clone(),
                            )))),
                            Expression::string("object"),
                        ),
                        vec![Statement::new(StatementDesc::If(
                            Expression::bin(
                                BinOp::EqEqEq,
                                Expression::var(b),
                                Expression::string("One"),
                            ),
                            vec![
                                Statement::exp(Expression::call(
                                    console_log.clone(),
                                    vec![Expression::string("aaa")],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![],
                        ))],
                        vec![],
                    )),
                    Statement::exp(Expression::call(
                        console_log,
                        vec![Expression::string("twwwoooo")],
                        CallInfo::default(),
                    )),
                    Statement::return_(Expression::undefined(true)),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (typeof b !== \"object\") {"),
            "{rendered}"
        );
        assert!(rendered.contains("if (b === \"One\") {"), "{rendered}");
        assert!(rendered.contains("console.log(\"aaa\");"), "{rendered}");
        assert!(rendered.contains("} else {"), "{rendered}");
        assert!(
            rendered.contains("console.log(\"twwwoooo\");"),
            "{rendered}"
        );
        assert!(rendered.contains("return;"), "{rendered}");
        assert!(!rendered.contains("&&"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_tail_merges_shared_else_guard_like_ocaml() {
        let handle = Ident::create_local("handle");
        let outer = Ident::create_local("outer");
        let value = Ident::create_local("value");
        let yes = Ident::create_local("yes");
        let no = Ident::create_local("no");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![outer.clone(), value.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    Expression::var(outer.clone()),
                    vec![
                        Statement::new(StatementDesc::If(
                            Expression::bin(
                                BinOp::NotEqEq,
                                Expression::var(value.clone()),
                                Expression::number(Number::int(3)),
                            ),
                            vec![
                                Statement::exp(Expression::call(
                                    Expression::var(no.clone()),
                                    vec![],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![],
                        )),
                        Statement::exp(Expression::call(
                            Expression::var(yes),
                            vec![],
                            CallInfo::default(),
                        )),
                        Statement::return_(Expression::undefined(true)),
                    ],
                    vec![
                        Statement::exp(Expression::call(
                            Expression::var(no),
                            vec![],
                            CallInfo::default(),
                        )),
                        Statement::return_(Expression::undefined(true)),
                    ],
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (outer && value === 3) {"));
        assert!(rendered.contains("yes();"));
        assert!(rendered.contains("} else {"));
        assert!(rendered.contains("no();"));
        assert!(!rendered.contains("if (value !== 3)"));
        assert!(!rendered.contains("return;"));
    }

    #[test]
    fn test_print_unit_function_tail_merges_shared_else_positive_guard_like_iterator_tests() {
        let handle = Ident::create_local("handle");
        let value = Ident::create_local("value");
        let done = Ident::create_local("done");
        let next = Ident::create_local("next");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: handle,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![value.clone()],
                body: vec![Statement::new(StatementDesc::If(
                    Expression::bin(
                        BinOp::NotEqEq,
                        Expression::var(value.clone()),
                        Expression::undefined(false),
                    ),
                    vec![
                        Statement::new(StatementDesc::If(
                            Expression::bin(
                                BinOp::EqEqEq,
                                Expression::var(value.clone()),
                                Expression::number(Number::int(3)),
                            ),
                            vec![
                                Statement::exp(Expression::call(
                                    Expression::var(done),
                                    vec![],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![],
                        )),
                        Statement::exp(Expression::call(
                            Expression::var(next.clone()),
                            vec![],
                            CallInfo::default(),
                        )),
                        Statement::return_(Expression::undefined(true)),
                    ],
                    vec![
                        Statement::exp(Expression::call(
                            Expression::var(next),
                            vec![],
                            CallInfo::default(),
                        )),
                        Statement::return_(Expression::undefined(true)),
                    ],
                ))],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (value === 3) {"), "{rendered}");
        assert!(rendered.contains("done();"), "{rendered}");
        assert!(rendered.contains("} else {"), "{rendered}");
        assert!(rendered.contains("next();"), "{rendered}");
        assert!(!rendered.contains("if (value !== undefined)"), "{rendered}");
        assert!(!rendered.contains("return;"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_merges_implicit_shared_tail_into_nested_if_else_like_ocaml() {
        let do_with_b = Ident::create_local("doWithB");
        let console_log = Expression::qualified(
            ModuleId {
                id: Ident::create_local("console"),
                kind: Kind::External {
                    name: "console".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            Some("log".to_string()),
        );
        let b = Ident::create_local("b");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: do_with_b,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![b.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                                b.clone(),
                            )))),
                            Expression::string("object"),
                        ),
                        vec![Statement::new(StatementDesc::If(
                            Expression::bin(
                                BinOp::EqEqEq,
                                Expression::var(b),
                                Expression::string("One"),
                            ),
                            vec![
                                Statement::exp(Expression::call(
                                    console_log.clone(),
                                    vec![Expression::string("aaa")],
                                    CallInfo::default(),
                                )),
                                Statement::return_(Expression::undefined(true)),
                            ],
                            vec![],
                        ))],
                        vec![],
                    )),
                    Statement::exp(Expression::call(
                        console_log,
                        vec![Expression::string("twwwoooo")],
                        CallInfo::default(),
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (typeof b !== \"object\") {"),
            "{rendered}"
        );
        assert!(rendered.contains("if (b === \"One\") {"), "{rendered}");
        assert!(rendered.contains("console.log(\"aaa\");"), "{rendered}");
        assert!(
            rendered.contains("console.log(\"twwwoooo\");"),
            "{rendered}"
        );
        assert!(rendered.contains("return;"), "{rendered}");
        assert!(!rendered.contains("&&"), "{rendered}");
        assert!(rendered.contains("} else {"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_merges_implicit_terminal_outer_else_like_do_with_a() {
        let do_with_a = Ident::create_local("doWithA");
        let console_log = Expression::qualified(
            ModuleId {
                id: Ident::create_local("console"),
                kind: Kind::External {
                    name: "console".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            Some("log".to_string()),
        );
        let a = Ident::create_local("a");
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: do_with_a,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![a.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::NotEqEq,
                            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                                a.clone(),
                            )))),
                            Expression::string("object"),
                        ),
                        vec![
                            Statement::new(StatementDesc::If(
                                Expression::bin(
                                    BinOp::EqEqEq,
                                    Expression::var(a),
                                    Expression::string("One"),
                                ),
                                vec![
                                    Statement::exp(Expression::call(
                                        console_log.clone(),
                                        vec![Expression::string("aaa")],
                                        CallInfo::default(),
                                    )),
                                    Statement::return_(Expression::undefined(true)),
                                ],
                                vec![],
                            )),
                            Statement::exp(Expression::call(
                                console_log.clone(),
                                vec![Expression::string("threeeee")],
                                CallInfo::default(),
                            )),
                            Statement::return_(Expression::undefined(true)),
                        ],
                        vec![],
                    )),
                    Statement::exp(Expression::call(
                        console_log,
                        vec![Expression::string("twwwoooo")],
                        CallInfo::default(),
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered.contains("if (typeof a !== \"object\") {"),
            "{rendered}"
        );
        assert!(rendered.contains("if (a === \"One\") {"), "{rendered}");
        assert!(
            rendered.contains("console.log(\"threeeee\");"),
            "{rendered}"
        );
        assert!(rendered.contains("} else {"), "{rendered}");
        assert!(
            rendered.contains("console.log(\"twwwoooo\");"),
            "{rendered}"
        );
        assert!(rendered.contains("return;"), "{rendered}");
    }

    #[test]
    fn test_print_unit_function_body_merges_implicit_shared_else_guard_chain_like_gpr_1891() {
        let foo = Ident::create_local("foo");
        let x = Ident::create_local("x");
        let console_log = Expression::qualified(
            ModuleId {
                id: Ident::create_local("console"),
                kind: Kind::External {
                    name: "console".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            Some("log".to_string()),
        );
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: foo,
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![x.clone()],
                body: vec![
                    Statement::new(StatementDesc::If(
                        Expression::bin(
                            BinOp::EqEqEq,
                            Expression::new(ExpressionDesc::Typeof(Box::new(Expression::var(
                                x.clone(),
                            )))),
                            Expression::string("object"),
                        ),
                        vec![
                            Statement::new(StatementDesc::If(
                                Expression::bin(
                                    BinOp::EqEqEq,
                                    Expression::new(ExpressionDesc::StaticIndex(
                                        Box::new(Expression::var(x.clone())),
                                        "NAME".to_string(),
                                        None,
                                    )),
                                    Expression::string("Foo"),
                                ),
                                vec![
                                    Statement::new(StatementDesc::If(
                                        Expression::bin(
                                            BinOp::NotEqEq,
                                            Expression::new(ExpressionDesc::StaticIndex(
                                                Box::new(Expression::var(x.clone())),
                                                "VAL".to_string(),
                                                None,
                                            )),
                                            Expression::number(Number::int(3)),
                                        ),
                                        vec![
                                            Statement::exp(Expression::call(
                                                console_log.clone(),
                                                vec![Expression::string("2")],
                                                CallInfo::default(),
                                            )),
                                            Statement::return_(Expression::undefined(true)),
                                        ],
                                        vec![],
                                    )),
                                    Statement::exp(Expression::call(
                                        console_log.clone(),
                                        vec![Expression::string("1")],
                                        CallInfo::default(),
                                    )),
                                    Statement::return_(Expression::undefined(true)),
                                ],
                                vec![],
                            )),
                            Statement::exp(Expression::call(
                                console_log.clone(),
                                vec![Expression::string("2")],
                                CallInfo::default(),
                            )),
                            Statement::return_(Expression::undefined(true)),
                        ],
                        vec![],
                    )),
                    Statement::exp(Expression::call(
                        console_log,
                        vec![Expression::string("2")],
                        CallInfo::default(),
                    )),
                ],
                env: Default::default(),
                return_unit: true,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(
            rendered
                .contains("if (typeof x === \"object\" && x.NAME === \"Foo\" && x.VAL === 3) {"),
            "{rendered}"
        );
        assert!(rendered.contains("console.log(\"1\");"), "{rendered}");
        assert!(rendered.contains("} else {"), "{rendered}");
        assert!(rendered.contains("console.log(\"2\");"), "{rendered}");
        assert!(!rendered.contains("if (x.NAME === \"Foo\")"), "{rendered}");
        assert!(!rendered.contains("x.VAL !== 3"), "{rendered}");
        assert!(!rendered.contains("return;"), "{rendered}");
    }

    #[test]
    fn test_print_variable_declaration_omits_undefined_initializer() {
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: Ident::create_local("VS"),
            value: Some(Expression::undefined(false)),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert_eq!(rendered, "let VS;");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_dead_pure_variable_declaration_is_omitted_like_ocaml() {
        let mut dead_info = IdentInfo::default();
        dead_info.used_stats = UsedStats::DeadPure;

        let rendered = print_block(&vec![
            Statement::variable(VariableDeclaration {
                ident: Ident::create_local("dead"),
                value: Some(Expression::array(
                    vec![Expression::number(Number::int(1))],
                    MutableFlag::Immutable,
                )),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: dead_info,
            }),
            Statement::variable(VariableDeclaration {
                ident: Ident::create_local("alive"),
                value: Some(Expression::number(Number::int(2))),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert_eq!(rendered, "let alive = 2;");
    }

    #[test]
    fn test_print_dead_non_pure_variable_declaration_as_expression_like_ocaml() {
        let mut dead_info = IdentInfo::default();
        dead_info.used_stats = UsedStats::DeadNonPure;
        let effect = Ident::create_local("effect");

        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: Ident::create_local("dead"),
            value: Some(Expression::call(
                Expression::var(effect),
                vec![],
                CallInfo::default(),
            )),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: dead_info,
        })]);

        assert_eq!(rendered, "effect();");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_dead_pure_top_level_function_binding_is_omitted_like_ocaml() {
        let mut dead_info = IdentInfo::default();
        dead_info.used_stats = UsedStats::DeadPure;

        let rendered = print_block(&vec![
            Statement::variable(VariableDeclaration {
                ident: Ident::create_local("deadFn"),
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![],
                    body: vec![Statement::return_(Expression::number(Number::int(1)))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: dead_info,
            }),
            Statement::variable(VariableDeclaration {
                ident: Ident::create_local("alive"),
                value: Some(Expression::number(Number::int(2))),
                property: crate::lambda::lam_compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert_eq!(rendered, "let alive = 2;");
    }

    #[test]
    fn test_print_property_access_uses_dot_for_default_keyword() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(Ident::create_local("Es6_export"))),
            "default".to_string(),
            None,
        )));

        assert_eq!(rendered, "Es6_export.default");
    }

    #[test]
    fn test_print_property_access_unwraps_uppercase_exotic_keys() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::var(Ident::create_local("x"))),
            "\\\"MyWeirdProp\"".to_string(),
            None,
        )));

        assert_eq!(rendered, "x.MyWeirdProp");
    }

    #[test]
    fn test_print_object_literal_unwraps_uppercase_exotic_keys() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Object(
            None,
            vec![(
                PropertyName::Lit("\\\"MyWeirdProp\"".to_string()),
                Expression::number(Number::int(1)),
            )],
        )));

        assert_eq!(rendered, "{\n  MyWeirdProp: 1\n}");
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_print_parenthesized_object_literal_preserves_group_indentation_like_ocaml() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::ArrayIndex(
            Box::new(Expression::new(ExpressionDesc::Object(
                None,
                vec![
                    (
                        PropertyName::lit("foo"),
                        Expression::number(Number::int(43)),
                    ),
                    (
                        PropertyName::lit("bar"),
                        Expression::number(Number::int(86)),
                    ),
                ],
            ))),
            Box::new(Expression::string("foo")),
        )));

        assert_eq!(rendered, "({\n  foo: 43,\n  bar: 86\n})[\"foo\"]");
    }

    #[test]
    fn test_print_parenthesized_object_literal_before_dot_access_preserves_group_indentation_like_ocaml()
     {
        let expr = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::new(ExpressionDesc::Object(
                None,
                vec![(PropertyName::lit("_5"), Expression::number(Number::int(3)))],
            ))),
            "TAG".to_string(),
            None,
        ));

        assert_eq!(print_expression(&expr), "({\n  _5: 3\n}).TAG");
    }

    #[test]
    fn test_print_object_literal_call_argument_before_index_keeps_group_indent_like_ocaml() {
        let expr = Expression::new(ExpressionDesc::ArrayIndex(
            Box::new(Expression::call(
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(Expression::var(Ident::create_local("Object"))),
                    "create".to_string(),
                    None,
                )),
                vec![Expression::new(ExpressionDesc::Object(
                    None,
                    vec![(PropertyName::lit("a"), Expression::number(Number::int(1)))],
                ))],
                CallInfo::default(),
            )),
            Box::new(Expression::string("a")),
        ));

        assert_eq!(
            print_expression(&expr),
            "$$Object.create({\n    a: 1\n  })[\"a\"]"
        );
    }

    #[test]
    fn test_print_parenthesized_object_literal_index_as_call_argument_keeps_group_indent() {
        let arg = Expression::new(ExpressionDesc::ArrayIndex(
            Box::new(Expression::new(ExpressionDesc::Object(
                None,
                vec![
                    (
                        PropertyName::lit("foo"),
                        Expression::number(Number::int(43)),
                    ),
                    (
                        PropertyName::lit("bar"),
                        Expression::number(Number::int(86)),
                    ),
                ],
            ))),
            Box::new(Expression::string("foo")),
        ));
        let call = Expression::call(
            Expression::var(Ident::create_local("f")),
            vec![arg],
            CallInfo::default(),
        );

        assert_eq!(
            print_expression(&call),
            "f(({\n    foo: 43,\n    bar: 86\n  })[\"foo\"])"
        );
    }

    #[test]
    fn test_print_parenthesized_object_literal_dot_access_as_call_argument_preserves_base_indent() {
        let arg = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(Expression::new(ExpressionDesc::Object(
                None,
                vec![(PropertyName::lit("_5"), Expression::number(Number::int(3)))],
            ))),
            "TAG".to_string(),
            None,
        ));
        let call = Expression::call(
            Expression::var(Ident::create_local("f")),
            vec![arg],
            CallInfo::default(),
        );

        assert_eq!(print_expression(&call), "f(({\n  _5: 3\n}).TAG)");
    }

    #[test]
    fn test_print_caml_block_tag_call_argument_uses_group_indent_like_ocaml() {
        let call = Expression::call(
            Expression::new(ExpressionDesc::StaticIndex(
                Box::new(Expression::var(Ident::create_local("console"))),
                "log".to_string(),
                None,
            )),
            vec![Expression::new(ExpressionDesc::CamlBlockTag(
                Box::new(Expression::new(ExpressionDesc::Object(
                    None,
                    vec![(PropertyName::lit("_5"), Expression::number(Number::int(3)))],
                ))),
                "TAG".to_string(),
            ))],
            CallInfo::default(),
        );

        assert_eq!(
            print_expression(&call),
            "console.log(({\n    _5: 3\n  }).TAG)"
        );
    }

    #[test]
    fn test_print_nested_member_target_call_with_multiline_array_arg_avoids_double_indent() {
        let promise_all = Expression::call(
            Expression::new(ExpressionDesc::StaticIndex(
                Box::new(Expression::var(Ident::create_local("Promise"))),
                "all".to_string(),
                None,
            )),
            vec![Expression::array(
                vec![
                    Expression::var(Ident::create_local("p1")),
                    Expression::var(Ident::create_local("p2")),
                    Expression::var(Ident::create_local("p3")),
                ],
                MutableFlag::Immutable,
            )],
            CallInfo::default(),
        );
        let stmt = Statement::new(StatementDesc::If(
            Expression::bool(true),
            vec![Statement::return_(Expression::new(
                ExpressionDesc::StaticIndex(Box::new(promise_all), "then".to_string(), None),
            ))],
            vec![],
        ));

        assert_eq!(
            print_block(&vec![stmt]),
            "if (true) {\n  return $$Promise.all([\n    p1,\n    p2,\n    p3\n  ]).then;\n}"
        );
    }

    #[test]
    fn test_print_new_call_with_multiline_array_argument_keeps_array_layout() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::New(
            Box::new(Expression::var(Ident::create_local("BigInt64Array"))),
            Some(vec![Expression::array(
                vec![
                    Expression::var(Ident::create_local("num1")),
                    Expression::var(Ident::create_local("num2")),
                ],
                MutableFlag::Immutable,
            )]),
        )));

        assert!(rendered.starts_with("new $$BigInt64Array(["));
        assert!(rendered.contains("[\n  num1,\n  num2\n])"));
    }

    #[test]
    fn test_print_new_index_call_argument_keeps_multiline_array_group_indent_like_ocaml() {
        let arg = Expression::new(ExpressionDesc::ArrayIndex(
            Box::new(Expression::new(ExpressionDesc::New(
                Box::new(Expression::var(Ident::create_local("BigInt64Array"))),
                Some(vec![Expression::array(
                    vec![
                        Expression::var(Ident::create_local("num1")),
                        Expression::var(Ident::create_local("num2")),
                    ],
                    MutableFlag::Immutable,
                )]),
            ))),
            Box::new(Expression::number(Number::int(1))),
        ));
        let call = Expression::call(
            Expression::var(Ident::create_local("f")),
            vec![arg],
            CallInfo::default(),
        );

        assert_eq!(
            print_expression(&call),
            "f(new $$BigInt64Array([\n    num1,\n    num2\n  ])[1])"
        );
    }

    #[test]
    fn test_print_indexed_multiline_array_call_argument_uses_group_indent_like_ocaml() {
        let arg = Expression::new(ExpressionDesc::ArrayIndex(
            Box::new(Expression::array(
                vec![
                    Expression::number(Number::int(0)),
                    Expression::number(Number::int(1)),
                    Expression::number(Number::int(2)),
                ],
                MutableFlag::Immutable,
            )),
            Box::new(Expression::number(Number::int(10))),
        ));
        let call = Expression::call(
            Expression::var(Ident::create_local("f")),
            vec![arg],
            CallInfo::default(),
        );

        assert_eq!(
            print_expression(&call),
            "f([\n    0,\n    1,\n    2\n  ][10])"
        );
    }

    #[test]
    fn test_print_length_of_member_target_call_with_multiline_array_arg_preserves_base_indent() {
        let arg = Expression::length(
            Expression::call(
                Expression::var(Ident::create_local("g")),
                vec![Expression::array(
                    vec![
                        Expression::number(Number::int(1)),
                        Expression::number(Number::int(2)),
                        Expression::number(Number::int(3)),
                    ],
                    MutableFlag::Immutable,
                )],
                CallInfo::default(),
            ),
            LengthObject::Array,
        );
        let call = Expression::call(
            Expression::var(Ident::create_local("f")),
            vec![arg],
            CallInfo::default(),
        );

        assert_eq!(
            print_expression(&call),
            "f(g([\n  1,\n  2,\n  3\n]).length)"
        );
    }

    #[test]
    fn test_print_static_member_target_new_with_multiline_array_arg_preserves_base_indent() {
        let map_entries = Expression::array(
            vec![
                Expression::array(
                    vec![
                        Expression::number(Number::int(1)),
                        Expression::number(Number::int(3)),
                    ],
                    MutableFlag::Immutable,
                ),
                Expression::array(
                    vec![
                        Expression::number(Number::int(2)),
                        Expression::number(Number::int(4)),
                    ],
                    MutableFlag::Immutable,
                ),
            ],
            MutableFlag::Immutable,
        );
        let values_call = Expression::call(
            Expression::new(ExpressionDesc::StaticIndex(
                Box::new(Expression::new(ExpressionDesc::New(
                    Box::new(Expression::var(Ident::create_local("Map"))),
                    Some(vec![map_entries]),
                ))),
                "values".to_string(),
                None,
            )),
            vec![],
            CallInfo::default(),
        );
        let call = Expression::call(
            Expression::var(Ident::create_local("f")),
            vec![values_call],
            CallInfo::default(),
        );

        assert_eq!(
            print_expression(&call),
            "f(new $$Map([\n  [\n    1,\n    3\n  ],\n  [\n    2,\n    4\n  ]\n]).values())"
        );
    }

    #[test]
    fn test_print_qualified_runtime_member_mangles_reserved_name() {
        let rendered = print_expression(&Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Js_promise2"),
                kind: Kind::Runtime,
                dynamic_import: false,
            },
            Some("catch".to_string()),
        ));

        assert_eq!(rendered, "Js_promise2.$$catch");
    }

    #[test]
    fn test_print_qualified_external_member_preserves_js_property_access() {
        let rendered = print_expression(&Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("URL"),
                kind: Kind::External {
                    name: "url".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            Some("catch".to_string()),
        ));

        assert_eq!(rendered, "URL.catch");
    }

    #[test]
    fn test_print_object_literal_allows_keyword_property_names_without_quotes() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Object(
            None,
            vec![
                (
                    PropertyName::lit("catch"),
                    Expression::number(Number::int(1)),
                ),
                (
                    PropertyName::lit("default"),
                    Expression::number(Number::int(2)),
                ),
            ],
        )));

        assert_eq!(rendered, "{\n  catch: 1,\n  default: 2\n}");
    }

    #[test]
    fn test_print_spread_only_object_literal_inline_like_ocaml() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Object(
            Some(Box::new(Expression::var(Ident::create_local("source")))),
            vec![],
        )));

        assert_eq!(rendered, "{...source}");
    }

    #[test]
    fn test_print_function_declaration_preserves_raw_directive() {
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: Ident::create_local("testFnWithDirective"),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![Ident::create_local("name")],
                body: vec![Statement::return_(Expression::string("Hello"))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: Some("'use memo'".to_string()),
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains(
            "function testFnWithDirective(name) {\n  'use memo';\n  return \"Hello\";\n}"
        ));
    }

    #[test]
    fn test_print_function_expression_preserves_raw_directive() {
        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![Ident::create_local("name")],
            body: vec![Statement::return_(Expression::string("Hello"))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: Some("'use cache'".to_string()),
        }));

        assert_eq!(
            rendered,
            "name => {\n  'use cache';\n  return \"Hello\";\n}"
        );
    }

    #[test]
    fn test_print_method_function_expression_omits_the_this_parameter() {
        let this_param = Ident::create_local("me");
        let amount = Ident::create_local("amount");

        let rendered = print_expression(&Expression::new(ExpressionDesc::Fun {
            is_method: true,
            params: vec![this_param.clone(), amount],
            body: vec![Statement::return_(Expression::var(this_param))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }));

        assert_eq!(
            rendered,
            "function (amount) {\n  let me = this ;\n  return me;\n}"
        );
    }

    #[test]
    fn test_print_top_level_method_function_as_named_declaration() {
        let this_param = Ident::create_local("self");
        let value = Ident::create_local("value");

        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: Ident::create_local("methodWithThis"),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: true,
                params: vec![this_param.clone(), value.clone()],
                body: vec![Statement::return_(Expression::var(this_param))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: crate::lambda::lam_compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert_eq!(
            rendered,
            "function methodWithThis(value) {\n  let self = this ;\n  return self;\n}"
        );
    }

    #[test]
    fn test_print_cons_constructor_as_hd_tl_object() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![
                Expression::number(Number::int(1)),
                Expression::number(Number::int(0)),
            ],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::constructor("::", 1, 0),
        ));

        assert_eq!(print_expression(&expr), "{\n  hd: 1,\n  tl: 0\n}");
    }

    #[test]
    fn test_print_non_cons_constructor_keeps_tag_object_shape() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::number(Number::int(1))],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::constructor("Some", 1, 0),
        ));

        assert_eq!(print_expression(&expr), "{\n  TAG: \"Some\",\n  _0: 1\n}");
    }

    #[test]
    fn test_print_non_cons_constructor_adds_debug_name_symbol_in_debug_mode() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![
                Expression::number(Number::int(1)),
                Expression::number(Number::int(2)),
            ],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::constructor("A", 2, 0),
        ));

        assert_eq!(
            print_expression_with_debug(&expr, true),
            "{\n  TAG: \"A\",\n  _0: 1,\n  _1: 2,\n  [Symbol.for(\"name\")]: \"A\"\n}"
        );
        assert_eq!(
            print_expression_with_debug(&expr, false),
            "{\n  TAG: \"A\",\n  _0: 1,\n  _1: 2\n}"
        );
    }

    #[test]
    fn test_print_record_omits_optional_undefined_fields() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![
                Expression::number(Number::int(10)),
                Expression::undefined(false),
            ],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::record(
                vec![("x".to_string(), false), ("i".to_string(), true)],
                crate::parser::ast::MutableFlag::Immutable,
            ),
        ));

        assert_eq!(print_expression(&expr), "{\n  x: 10\n}");
    }

    #[test]
    fn test_print_inline_record_variant_keeps_tag_field() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::string("hello")],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::RecordInlined {
                name: "One".to_string(),
                num_nonconst: 1,
                tag: 0,
                fields: vec![("name".to_string(), false)],
                logical_field_count: None,
                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                attrs: vec![],
            },
        ));

        assert_eq!(
            print_expression(&expr),
            "{\n  TAG: \"One\",\n  name: \"hello\"\n}"
        );
    }

    #[test]
    fn test_print_numeric_named_record_as_array() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![
                Expression::number(Number::int(1)),
                Expression::number(Number::int(2)),
            ],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::record(
                vec![("0".to_string(), false), ("1".to_string(), false)],
                crate::parser::ast::MutableFlag::Immutable,
            ),
        ));

        assert_eq!(print_expression(&expr), "[\n  1,\n  2\n]");
    }

    #[test]
    fn test_print_module_block_uses_object_layout() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::number(Number::int(1))],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Module(vec!["value".to_string()]),
        ));

        assert_eq!(print_expression(&expr), "{\n  value: 1\n}");
    }

    #[test]
    fn test_print_exception_extension_block_as_object() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::string("Not_found")],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Extension,
        ));

        assert_eq!(print_expression(&expr), "{\n  RE_EXN_ID: \"Not_found\"\n}");
    }

    #[test]
    fn test_print_record_extension_exception_uses_named_fields() {
        let expr = Expression::new(ExpressionDesc::CamlBlock(
            vec![
                Expression::var(Ident::create_local("A")),
                Expression::number(Number::int(3)),
            ],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::RecordExt {
                fields: vec!["value".to_string()],
                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
            },
        ));

        assert_eq!(print_expression(&expr), "{\n  RE_EXN_ID: A,\n  value: 3\n}");
    }

    #[test]
    fn test_print_throw_exception_block_includes_error_stack() {
        let rendered = print_block(&vec![Statement::throw(Expression::new(
            ExpressionDesc::CamlBlock(
                vec![Expression::string("Not_found")],
                MutableFlag::Immutable,
                Box::new(Expression::number(Number::int(0))),
                TagInfo::Extension,
            ),
        ))]);

        assert_eq!(
            rendered,
            "throw {\n  RE_EXN_ID: \"Not_found\",\n  Error: new Error()\n};"
        );
    }

    #[test]
    fn test_print_int_switch_cases_keep_space_before_colon() {
        let rendered = print_block(&vec![Statement::new(StatementDesc::IntSwitch(
            Expression::var(Ident::create_local("tag")),
            vec![
                (
                    0,
                    CaseClause {
                        body: vec![Statement::return_(Expression::number(Number::int(1)))],
                        should_break: false,
                        comment: None,
                    },
                ),
                (
                    1,
                    CaseClause {
                        body: vec![],
                        should_break: false,
                        comment: None,
                    },
                ),
            ],
            Some(vec![Statement::return_(Expression::number(Number::int(2)))]),
        ))]);

        assert_eq!(
            rendered,
            "switch (tag) {\n  case 0 :\n    return 1;\n  case 1 :\n  default:\n    return 2;\n}"
        );
    }

    #[test]
    fn test_print_int_switch_cases_emit_break_for_empty_body_clauses() {
        let rendered = print_block(&vec![Statement::new(StatementDesc::IntSwitch(
            Expression::var(Ident::create_local("tag")),
            vec![
                (
                    0,
                    CaseClause {
                        body: vec![],
                        should_break: false,
                        comment: None,
                    },
                ),
                (
                    1,
                    CaseClause {
                        body: vec![],
                        should_break: true,
                        comment: None,
                    },
                ),
            ],
            None,
        ))]);

        assert_eq!(
            rendered,
            "switch (tag) {\n  case 0 :\n  case 1 :\n    break;\n}"
        );
    }

    #[test]
    fn test_print_string_switch_cases_keep_space_before_colon() {
        let rendered = print_block(&vec![Statement::new(StatementDesc::StringSwitch(
            Expression::var(Ident::create_local("tag")),
            vec![
                StringClause {
                    tag_type: SwitchCaseTag::String("One".to_string()),
                    clause: CaseClause {
                        body: vec![Statement::return_(Expression::number(Number::int(1)))],
                        should_break: false,
                        comment: None,
                    },
                },
                StringClause {
                    tag_type: SwitchCaseTag::String("Two".to_string()),
                    clause: CaseClause {
                        body: vec![],
                        should_break: false,
                        comment: None,
                    },
                },
            ],
            Some(vec![Statement::return_(Expression::number(Number::int(2)))]),
        ))]);

        assert_eq!(
            rendered,
            "switch (tag) {\n  case \"One\" :\n    return 1;\n  case \"Two\" :\n  default:\n    return 2;\n}"
        );
    }

    #[test]
    fn test_print_string_switch_cases_emit_break_for_empty_body_clauses() {
        let rendered = print_block(&vec![Statement::new(StatementDesc::StringSwitch(
            Expression::var(Ident::create_local("tag")),
            vec![
                StringClause {
                    tag_type: SwitchCaseTag::String("One".to_string()),
                    clause: CaseClause {
                        body: vec![],
                        should_break: false,
                        comment: None,
                    },
                },
                StringClause {
                    tag_type: SwitchCaseTag::String("Two".to_string()),
                    clause: CaseClause {
                        body: vec![],
                        should_break: true,
                        comment: None,
                    },
                },
            ],
            None,
        ))]);

        assert_eq!(
            rendered,
            "switch (tag) {\n  case \"One\" :\n  case \"Two\" :\n    break;\n}"
        );
    }

    #[test]
    fn test_print_string_switch_cases_keep_break_on_its_own_line_after_body() {
        let rendered = print_block(&vec![Statement::new(StatementDesc::StringSwitch(
            Expression::var(Ident::create_local("tag")),
            vec![StringClause {
                tag_type: SwitchCaseTag::String("One".to_string()),
                clause: CaseClause {
                    body: vec![Statement::exp(Expression::call(
                        Expression::qualified(
                            ModuleId {
                                id: Ident::create_local("console"),
                                kind: Kind::Ml,
                                dynamic_import: false,
                            },
                            Some("log".to_string()),
                        ),
                        vec![Expression::string("hello")],
                        CallInfo::default(),
                    ))],
                    should_break: true,
                    comment: None,
                },
            }],
            None,
        ))]);

        assert_eq!(
            rendered,
            "switch (tag) {\n  case \"One\" :\n    console.log(\"hello\");\n    break;\n}"
        );
    }

    #[test]
    fn test_print_string_switch_cases_preserve_marshaled_string_tags() {
        let rendered = print_block(&vec![Statement::new(StatementDesc::StringSwitch(
            Expression::var(Ident::create_local("tag")),
            vec![
                StringClause {
                    tag_type: SwitchCaseTag::String("\\\"".to_string()),
                    clause: CaseClause {
                        body: vec![Statement::return_(Expression::number(Number::int(1)))],
                        should_break: false,
                        comment: None,
                    },
                },
                StringClause {
                    tag_type: SwitchCaseTag::String("\\\\".to_string()),
                    clause: CaseClause {
                        body: vec![Statement::return_(Expression::number(Number::int(2)))],
                        should_break: false,
                        comment: None,
                    },
                },
            ],
            Some(vec![Statement::return_(Expression::number(Number::int(3)))]),
        ))]);

        assert_eq!(
            rendered,
            "switch (tag) {\n  case \"\\\"\" :\n    return 1;\n  case \"\\\\\" :\n    return 2;\n  default:\n    return 3;\n}"
        );
    }

    fn latin1_encoded_utf8(s: &str) -> String {
        s.as_bytes().iter().map(|&byte| char::from(byte)).collect()
    }
}
