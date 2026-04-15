//! JavaScript IR Printer - Generates JavaScript source code from JS IR.
//!
//! This module provides functionality to convert the JavaScript IR
//! into formatted JavaScript source code.

use super::op::{BinOp, Kind, Number, PropertyName, UsedStats};
use super::{
    Block, CallInfo, CaseClause, Delim, DepsProgram, Expression, ExpressionDesc, ForDirection,
    JsRawInfo, ModulePathResolver, Program, Statement, StatementDesc, StringClause, VIdent,
    VariableDeclaration,
};
use crate::binary_ast::ppx::{JsExpClassification, classify_js_exp};
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
    module_path_resolver: Option<ModulePathResolver>,
    /// Matches OCaml's `!Js_config.debug` toggle in the dumper.
    debug: bool,
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
        }
    }

    /// Create a new printer with module import resolution context.
    pub fn with_module_path_resolver(module_path_resolver: Option<&ModulePathResolver>) -> Self {
        Self::with_module_path_resolver_and_debug(module_path_resolver, false)
    }

    /// Create a new printer with module import resolution context and debug mode.
    pub fn with_module_path_resolver_and_debug(
        module_path_resolver: Option<&ModulePathResolver>,
        debug: bool,
    ) -> Self {
        let mut printer = Self::new();
        printer.module_path_resolver = module_path_resolver.cloned();
        printer.debug = debug;
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
    fn write(&mut self, s: &str) {
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
    fn write_char(&mut self, c: char) {
        self.output.push(c);
        self.last_new_line = false;
    }

    /// Write a newline with current indentation
    fn newline(&mut self) {
        if !self.last_new_line {
            self.output.push('\n');
            for _ in 0..self.indent {
                self.output.push_str(self.indent_str);
            }
            self.last_new_line = true;
        }
    }

    /// Match OCaml's Ext_pp.at_least_two_lines.
    fn at_least_two_lines(&mut self) {
        if !self.last_new_line {
            self.output.push('\n');
        }
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
    fn semi(&mut self) {
        self.output.push(';');
        self.last_new_line = false;
    }

    /// Increase indentation
    fn indent(&mut self) {
        self.indent += 1;
    }

    /// Decrease indentation
    fn dedent(&mut self) {
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
    fn ident_name(&mut self, id: &Ident) -> String {
        if let Some(name) = self.lookup_visible_name(id) {
            return name;
        }

        if id.stamp() == 0 {
            return id.name().to_string();
        }

        self.assign_scoped_ident_name(id, convert_ident_name(id.name()))
    }

    fn module_ident_name(&mut self, id: &Ident) -> String {
        if let Some(name) = self.lookup_visible_name(id) {
            return name;
        }

        let base = convert_ident_name(id.name());
        self.assign_scoped_ident_name(id, base)
    }

    /// Print a program
    pub fn print_program(&mut self, program: &Program) {
        self.at_least_two_lines();
        self.print_statements(&program.block, true);
    }

    /// Print a module-level program with headers, exports, and purity metadata.
    pub fn print_deps_program(&mut self, program: &DepsProgram) {
        self.print_deps_program_with_directives(program, &[]);
    }

    pub fn print_deps_program_with_directives(
        &mut self,
        program: &DepsProgram,
        directives: &[String],
    ) {
        for directive in directives {
            self.write(directive);
            self.newline();
        }
        self.write("// Generated by ReScript, PLEASE EDIT WITH CARE");
        self.newline();
        if deps_program_is_empty(program) {
            self.write(
                "/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */",
            );
            self.newline();
            return;
        }
        self.at_least_two_lines();
        let _printed_imports = self.print_module_imports(&program.modules);
        self.at_least_two_lines();
        self.print_statements(&program.program.block, true);

        self.at_least_two_lines();
        if !program.program.exports.is_empty() {
            self.print_esmodule_exports(&program.program.exports);
        }

        self.newline();
        match &program.side_effect {
            None => self.write("/* No side effect */"),
            Some(reason) => {
                let _ = write!(self.output, "/* {} Not a pure module */", reason);
                self.last_new_line = false;
            }
        }
        self.newline();
    }

    fn print_module_imports(&mut self, modules: &[super::ModuleId]) -> bool {
        let mut printed_any = false;

        for module in modules {
            let path = self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.resolve_module_path(module));
            let Some(path) = path else {
                continue;
            };

            if printed_any {
                self.newline();
            }

            self.write("import ");
            match &module.kind {
                Kind::External { default: true, .. } => {
                    let name = self.module_ident_name(&module.id);
                    self.write(&name);
                }
                _ => {
                    self.write("* as ");
                    let name = self.module_ident_name(&module.id);
                    self.write(&name);
                }
            }
            self.write(" from ");
            self.print_string(&path);

            if let Kind::External {
                import_attributes: Some(import_attributes),
                ..
            } = &module.kind
            {
                self.write(" with ");
                self.write("{");
                for (index, (key, value)) in import_attributes.entries.iter().enumerate() {
                    if index > 0 {
                        self.write(", ");
                    }
                    self.print_string(key);
                    self.write(": ");
                    self.print_string(value);
                }
                self.write("}");
            }

            self.semi();
            printed_any = true;
        }

        printed_any
    }

    /// Print statements
    pub fn print_statements(&mut self, stmts: &Block, top_level: bool) {
        let mut printed_any = false;
        for stmt in stmts {
            if !self.statement_prints_anything(stmt, top_level) {
                continue;
            }
            if printed_any {
                if top_level {
                    self.at_least_two_lines();
                } else {
                    self.newline();
                }
            }
            self.print_statement(stmt, top_level);
            printed_any = true;
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
            StatementDesc::Exp(expr) => !matches!(expr.desc, ExpressionDesc::Var(_)),
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
                self.print_expression(cond, 0);
                self.write(") ");
                self.print_brace_block(then_block);

                if !else_block.is_empty() {
                    self.write(" else ");
                    // Check if else block is just another if
                    if else_block.len() == 1 {
                        if let StatementDesc::If(_, _, _) = &else_block[0].desc {
                            self.print_statement(&else_block[0], false);
                            return;
                        }
                    }
                    self.print_brace_block(else_block);
                }
            }

            StatementDesc::While(cond, body) => {
                self.write("while ");
                self.write_char('(');
                self.print_expression(cond, 0);
                self.write(") ");
                self.print_brace_block(body);
                self.semi();
            }

            StatementDesc::ForRange(init, end, id, direction, body) => {
                let id_name = self.ident_name(id);
                self.with_local_ident_scope(std::slice::from_ref(&id_name), |this| {
                    let finish_binding = for_range_finish_needs_binding(end).then(|| {
                        this.fresh_scoped_name(format!("{}_finish", convert_ident_name(id.name())))
                    });

                    this.write("for ");
                    this.write_char('(');

                    match (init, finish_binding.as_deref()) {
                        (Some(init_expr), Some(finish_name)) => {
                            this.write("let ");
                            this.write(&id_name);
                            this.write(" = ");
                            this.print_expression(init_expr, 1);
                            this.write(", ");
                            this.write(finish_name);
                            this.write(" = ");
                            this.print_expression(end, 1);
                        }
                        (Some(init_expr), None) => {
                            this.write("let ");
                            this.write(&id_name);
                            this.write(" = ");
                            this.print_expression(init_expr, 1);
                        }
                        (None, Some(finish_name)) => {
                            this.write("let ");
                            this.write(finish_name);
                            this.write(" = ");
                            this.print_expression(end, 1);
                        }
                        (None, None) => {}
                    }

                    this.semi();
                    this.space();

                    this.write(&id_name);
                    match direction {
                        ForDirection::Upto => this.write(" <= "),
                        ForDirection::Downto => this.write(" >= "),
                        ForDirection::Up => this.write(" < "),
                    }
                    if let Some(finish_name) = finish_binding.as_deref() {
                        this.write(finish_name);
                    } else {
                        this.print_expression(end, 0);
                    }
                    this.semi();
                    this.space();

                    match direction {
                        ForDirection::Upto | ForDirection::Up => {
                            this.write("++");
                            this.write(&id_name);
                        }
                        ForDirection::Downto => {
                            this.write("--");
                            this.write(&id_name);
                        }
                    }

                    this.write(") ");
                    this.print_brace_block(body);
                });
            }

            StatementDesc::Continue => {
                self.write("continue");
                self.semi();
            }

            StatementDesc::Break => {
                self.write("break");
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
        if matches!(expr.desc, ExpressionDesc::Var(_)) {
            return;
        }
        let needs_paren = self.expr_needs_paren(expr);
        if needs_paren {
            self.write_char('(');
        }
        self.print_expression(expr, 0);
        if needs_paren {
            self.write_char(')');
        }
        self.semi();
    }

    /// Print a brace-enclosed block
    fn print_brace_block(&mut self, stmts: &Block) {
        self.write_char('{');
        if !stmts.is_empty() {
            self.indent();
            self.newline();
            self.print_statements(stmts, false);
            self.dedent();
            self.newline();
        }
        self.write_char('}');
    }

    /// Print a variable declaration
    fn print_variable_declaration(&mut self, decl: &VariableDeclaration) {
        let var_name = self.ident_name(&decl.ident);
        self.write("let ");
        self.write(&var_name);

        if let Some(value) = &decl.value {
            if !is_undefined_literal(value) {
                self.write(" = ");
                self.print_expression(value, 1);
            }
        }

        self.semi();
    }

    fn with_local_ident_scope<T>(
        &mut self,
        reserved_printed_names: &[String],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let mut scope = NameScope::default();
        for printed in reserved_printed_names {
            Self::reserve_printed_name(&mut scope, printed);
        }
        self.name_scopes.push(scope);
        let out = f(self);
        self.name_scopes.pop();
        out
    }

    fn with_function_ident_scope<T>(
        &mut self,
        params: &[Ident],
        body: &Block,
        function_ident: Option<&Ident>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let mut reserved_idents: Vec<Ident> =
            free_variables_of_block_with_defined(body, params.iter().cloned())
                .into_iter()
                .collect();
        if let Some(function_ident) = function_ident {
            reserved_idents.push(function_ident.clone());
        }
        reserved_idents.sort();
        reserved_idents.dedup();

        let reserved_printed_names = reserved_idents
            .into_iter()
            .map(|ident| self.ident_name(&ident))
            .collect::<Vec<_>>();

        self.with_local_ident_scope(&reserved_printed_names, f)
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

    fn print_esmodule_exports(&mut self, exports: &[Ident]) {
        self.write("export {");
        self.indent();
        for export in exports {
            self.newline();
            let local_name = self.ident_name(export);
            self.write(&local_name);
            let export_name = if export.name() == "default" {
                "default".to_string()
            } else {
                convert_ident_name(export.name())
            };
            if local_name != export_name {
                self.write(" as ");
                self.write(&export_name);
            }
            self.write_char(',');
        }
        self.dedent();
        self.newline();
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

        if !clause.body.is_empty() {
            self.indent();
            self.newline();
            self.print_statements(&clause.body, false);
            if clause.should_break {
                self.newline();
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

        if !clause.clause.body.is_empty() {
            self.indent();
            self.newline();
            self.print_statements(&clause.clause.body, false);
            if clause.clause.should_break {
                self.newline();
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

    fn collect_jsx_fields_from_object(
        &self,
        props: &[(PropertyName, Expression)],
    ) -> Option<Vec<(String, Expression)>> {
        let mut fields = Vec::with_capacity(props.len());
        for (name, value) in props {
            let PropertyName::Lit(name) = name else {
                return None;
            };
            fields.push((name.clone(), value.clone()));
        }
        Some(fields)
    }

    fn collect_jsx_fields_from_record_block(
        &self,
        elements: &[Expression],
        fields: &[(String, bool)],
    ) -> Option<Vec<(String, Expression)>> {
        if elements.len() != fields.len() {
            return None;
        }

        let mut collected = Vec::with_capacity(fields.len());
        for ((name, optional), value) in fields.iter().zip(elements.iter()) {
            if *optional && is_undefined_literal(value) {
                continue;
            }
            collected.push((name.clone(), value.clone()));
        }
        Some(collected)
    }

    fn collect_jsx_spread_assignments(
        &self,
        props: &Expression,
    ) -> Option<(Vec<(String, Expression)>, Expression)> {
        fn visit(
            expr: &Expression,
            acc: &mut Vec<(String, Expression)>,
        ) -> Option<Expression> {
            match &expr.desc {
                ExpressionDesc::Seq(first, rest) => match &first.desc {
                    ExpressionDesc::Bin(
                        BinOp::Eq,
                        target,
                        value,
                    ) => match &target.as_ref().desc {
                        ExpressionDesc::StaticIndex(_, name, _) => {
                            acc.push((name.clone(), value.as_ref().clone()));
                            visit(rest, acc)
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => Some(expr.clone()),
            }
        }

        let mut fields = Vec::new();
        let spread = visit(props, &mut fields)?;
        Some((fields, spread))
    }

    fn collect_transformed_jsx_props(
        &self,
        props: &Expression,
    ) -> Option<(Vec<(String, Expression)>, Option<Expression>)> {
        match &props.desc {
            ExpressionDesc::Object(dup, props) => Some((
                self.collect_jsx_fields_from_object(props)?,
                dup.as_ref().map(|dup| dup.as_ref().clone()),
            )),
            ExpressionDesc::CamlBlock(elements, _, _, crate::lambda::TagInfo::Record { fields, .. }) => {
                Some((
                    self.collect_jsx_fields_from_record_block(elements, fields)?,
                    None,
                ))
            }
            ExpressionDesc::Seq(_, _) => {
                let (fields, spread_props) = self.collect_jsx_spread_assignments(props)?;
                Some((fields, Some(spread_props)))
            }
            ExpressionDesc::Var(_) => Some((Vec::new(), Some(props.clone()))),
            _ => None,
        }
    }

    fn jsx_children(
        &self,
        fn_name: &str,
        fields: &[(String, Expression)],
        is_fragment: bool,
    ) -> Option<Vec<Expression>> {
        let children = fields.iter().find_map(|(name, expr)| {
            if name != "children" {
                return None;
            }

            if fn_name == "jsxs" {
                match &expr.desc {
                    ExpressionDesc::Array(children, _) => Some(children.clone()),
                    ExpressionDesc::OptionalBlock(inner, _) => match &inner.as_ref().desc {
                        ExpressionDesc::Array(children, _) => Some(children.clone()),
                        _ => Some(vec![expr.clone()]),
                    },
                    _ => Some(vec![expr.clone()]),
                }
            } else {
                Some(vec![expr.clone()])
            }
        });

        match children {
            None if is_fragment => Some(Vec::new()),
            other => other,
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
            ExpressionDesc::Call(_, _, CallInfo {
                call_transformed_jsx: true,
                ..
            })
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
        fields: &[(String, Expression)],
        spread_props: Option<&Expression>,
        key: Option<&Expression>,
    ) {
        let is_fragment = self.is_jsx_fragment_tag(tag);
        let children = self.jsx_children(fn_name, fields, is_fragment);
        let props: Vec<_> = fields
            .iter()
            .filter(|(name, _)| name != "children")
            .collect();
        let has_named_props = !props.is_empty();
        let printable_prop_count =
            usize::from(key.is_some()) + usize::from(spread_props.is_some()) + props.len();

        if level > 15 {
            self.write_char('(');
        }

        self.write("<");
        self.print_transformed_jsx_tag(tag, level, is_fragment);

        if printable_prop_count == 0 {
            if children.is_none() {
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
            for (index, (name, value)) in props.iter().enumerate() {
                self.print_transformed_jsx_named_prop(name, value);
                if index + 1 < props.len() {
                    self.newline();
                }
            }

            self.dedent();
        }

        match children {
            None => {
                if has_named_props {
                    self.newline();
                }
                self.write("/>");
            }
            Some(children) if children.is_empty() && is_fragment => {
                self.write("></>");
            }
            Some(children) => {
                if has_named_props {
                    self.newline();
                }
                self.write(">");
                self.indent();
                for child in &children {
                    self.newline();
                    self.print_transformed_jsx_child(child);
                }
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

        self.print_transformed_jsx(level, fn_name, tag, &fields, spread_props.as_ref(), key);
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
                    self.print_expression(arg, 1);
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
                        self.print_expression(arg, 1);
                    }
                }
                self.write_char(')');
                if needs_paren {
                    self.write_char(')');
                }
            }

            ExpressionDesc::ArrayIndex(arr, idx) => {
                let needs_paren = level > 15;
                if needs_paren {
                    self.write_char('(');
                }
                self.print_expression(arr, 15);
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
                self.print_expression(obj, 15);
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
                self.print_expression(e, 15);
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
                let use_arrow = !*is_method;
                self.with_function_ident_scope(params, body, None, |this| {
                    let (this_binding, param_names) =
                        this.method_params_and_binding(*is_method, params, body);

                    // Async prefix
                    if *async_ {
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

                    this.print_function_body_block(
                        body,
                        *return_unit,
                        directive.as_deref(),
                        this_binding.as_ref(),
                    );
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
                    TagInfo::PolyVar(name) => {
                        self.print_object_literal(
                            level,
                            None,
                            std::iter::once((false, None)).chain(
                                elements.get(1).into_iter().map(|value| (true, Some(value))),
                            ),
                            |this, (is_value, value)| {
                                if is_value {
                                    this.write("VAL: ");
                                    this.print_expression(
                                        value.expect("polyvar value property must exist"),
                                        1,
                                    );
                                } else {
                                    this.write("NAME: ");
                                    this.print_string(name);
                                }
                            },
                        );
                    }
                    _ => {
                        self.print_array_literal(elements);
                    }
                }
            }

            ExpressionDesc::CamlBlockTag(e, tag) => {
                self.print_expression(e, 15);
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

    fn print_array_literal(&mut self, elements: &[Expression]) {
        self.write_char('[');
        match elements {
            [] => {}
            [single] => self.print_expression(single, 1),
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
    fn print_string(&mut self, s: &str) {
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

    fn write_decoded_internal_string(&mut self, s: &str) {
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
        match &stmt.desc {
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

fn deps_program_is_empty(program: &DepsProgram) -> bool {
    program.modules.is_empty()
        && program.side_effect.is_none()
        && program.program.block.is_empty()
        && program.program.exports.is_empty()
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
        JsExpClassification::JsLiteral => false,
        JsExpClassification::JsFunction { .. } | JsExpClassification::JsExpUnknown => {
            !raw_snippet_exp_simple_enough(code)
        }
    }
}

fn tag_info_has_untagged(attrs: &[crate::lambda::tag_info::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.name == "unboxed")
}

fn tag_info_tag_name(attrs: &[crate::lambda::tag_info::Attribute]) -> Option<&str> {
    attrs.iter().find_map(|attr| {
        if attr.name != "tag" {
            return None;
        }
        match &attr.payload {
            crate::lambda::tag_info::AttributePayload::Str(value) => Some(value.as_str()),
            _ => None,
        }
    })
}

fn tag_info_runtime_tag(attrs: &[crate::lambda::tag_info::Attribute]) -> Option<SwitchCaseTag> {
    attrs.iter().find_map(|attr| {
        if attr.name != "as" {
            return None;
        }
        match &attr.payload {
            crate::lambda::tag_info::AttributePayload::Str(value) => {
                Some(SwitchCaseTag::String(value.clone()))
            }
            crate::lambda::tag_info::AttributePayload::Int(value) => {
                Some(SwitchCaseTag::Int(*value))
            }
            crate::lambda::tag_info::AttributePayload::Float(value) => {
                Some(SwitchCaseTag::Float(value.clone()))
            }
            crate::lambda::tag_info::AttributePayload::BigInt(value) => {
                Some(SwitchCaseTag::BigInt(value.clone()))
            }
            crate::lambda::tag_info::AttributePayload::Bool(value) => {
                Some(SwitchCaseTag::Bool(*value))
            }
            crate::lambda::tag_info::AttributePayload::Ident(value) if value == "null" => {
                Some(SwitchCaseTag::Null)
            }
            crate::lambda::tag_info::AttributePayload::Ident(value) if value == "undefined" => {
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
    matches!(
        block.as_slice(),
        [Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Undefined { .. },
                ..
            }),
            ..
        }]
    )
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
    if digits.is_empty() || digits.contains('.') || digits.contains('p') || digits.contains('P') {
        return None;
    }

    let value = u128::from_str_radix(&digits, 16).ok()?;
    let rendered = value.to_string();
    Some(if negative {
        format!("-{rendered}")
    } else {
        rendered
    })
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
        StatementDesc::While(cond, body) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(body, stats);
        }
        StatementDesc::ForRange(start, finish, loop_ident, _, body) => {
            if let Some(start) = start {
                collect_expression_idents(start, stats);
            }
            collect_expression_idents(finish, stats);
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
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
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

/// Print a program to a string
pub fn print_program(program: &Program) -> String {
    let mut printer = JsPrinter::new();
    printer.print_program(program);
    printer.into_output()
}

/// Print a module-level program to a string.
pub fn print_deps_program(
    program: &DepsProgram,
    module_path_resolver: Option<&ModulePathResolver>,
) -> String {
    print_deps_program_with_directives(program, module_path_resolver, &[], false)
}

pub fn print_deps_program_with_directives(
    program: &DepsProgram,
    module_path_resolver: Option<&ModulePathResolver>,
    directives: &[String],
    debug: bool,
) -> String {
    let mut printer = JsPrinter::with_module_path_resolver_and_debug(module_path_resolver, debug);
    printer.print_deps_program_with_directives(program, directives);
    printer.into_output()
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

        assert_eq!(print_expression(&expr), "<Foo.make />");
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
            print_expression(&expr),
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
            print_expression(&expr),
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
            print_expression(&expr),
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
    fn test_print_while() {
        let stmt = Statement::while_(Expression::bool(true), vec![Statement::break_()]);
        let result = print_block(&vec![stmt]);
        assert!(result.contains("while (true)"));
        assert!(result.contains("break;"));
    }

    #[test]
    fn test_print_for_range_complex_finish_uses_finish_binding() {
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let finish = Expression::new(ExpressionDesc::Length(
            Box::new(Expression::var(xs)),
            LengthObject::Array,
        ));
        let stmt = Statement::new(StatementDesc::ForRange(
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
    fn test_print_for_range_without_init_binds_complex_finish_once() {
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let finish = Expression::new(ExpressionDesc::Length(
            Box::new(Expression::var(xs)),
            LengthObject::Array,
        ));
        let stmt = Statement::new(StatementDesc::ForRange(
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
            property: crate::lambda::compat::LetKind::Strict,
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
            property: crate::lambda::compat::LetKind::Strict,
            ident_info: Default::default(),
        });
        let stmt_after = Statement::variable(VariableDeclaration {
            ident: after,
            value: Some(Expression::number(Number::int(2))),
            property: crate::lambda::compat::LetKind::Strict,
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
    fn test_print_function_scope_allows_shadowing_uncaptured_outer_name() {
        let outer = Ident::create_local("x");
        let foo = Ident::create_local("foo");
        let param = Ident::create_local("x");
        let rendered = print_block(&vec![
            Statement::variable(VariableDeclaration {
                ident: outer,
                value: Some(Expression::number(Number::int(1))),
                property: crate::lambda::compat::LetKind::Strict,
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
                property: crate::lambda::compat::LetKind::Strict,
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
                property: crate::lambda::compat::LetKind::Strict,
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
                property: crate::lambda::compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert!(rendered.contains("function foo(arg) {"));
        assert!(rendered.contains("return value + arg;"));
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
            property: crate::lambda::compat::LetKind::Strict,
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
            property: crate::lambda::compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert_eq!(rendered, "function n(prim) {\n  \n}");
    }

    #[test]
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
            property: crate::lambda::compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert!(rendered.contains("if (cond) {"));
        assert!(rendered.contains("console.log(\"hit\");"));
        assert!(!rendered.contains("else"));
        assert!(!rendered.contains("return;"));
    }

    #[test]
    fn test_print_variable_declaration_omits_undefined_initializer() {
        let rendered = print_block(&vec![Statement::variable(VariableDeclaration {
            ident: Ident::create_local("VS"),
            value: Some(Expression::undefined(false)),
            property: crate::lambda::compat::LetKind::Strict,
            ident_info: Default::default(),
        })]);

        assert_eq!(rendered, "let VS;");
    }

    #[test]
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
                property: crate::lambda::compat::LetKind::Strict,
                ident_info: dead_info,
            }),
            Statement::variable(VariableDeclaration {
                ident: Ident::create_local("alive"),
                value: Some(Expression::number(Number::int(2))),
                property: crate::lambda::compat::LetKind::Strict,
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
            property: crate::lambda::compat::LetKind::Strict,
            ident_info: dead_info,
        })]);

        assert_eq!(rendered, "effect();");
    }

    #[test]
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
                property: crate::lambda::compat::LetKind::Strict,
                ident_info: dead_info,
            }),
            Statement::variable(VariableDeclaration {
                ident: Ident::create_local("alive"),
                value: Some(Expression::number(Number::int(2))),
                property: crate::lambda::compat::LetKind::Strict,
                ident_info: Default::default(),
            }),
        ]);

        assert_eq!(rendered, "let alive = 2;");
    }

    #[test]
    fn test_print_empty_deps_program_uses_ocaml_empty_explanation() {
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(vec![], vec![]),
                modules: vec![],
                side_effect: None,
            },
            None,
        );
        assert_eq!(
            rendered,
            "// Generated by ReScript, PLEASE EDIT WITH CARE\n/* This output is empty. Its source's type definitions, externals and/or unused code got optimized away. */\n"
        );
    }

    #[test]
    fn test_print_deps_program_emits_top_level_directives_before_header() {
        let rendered = print_deps_program_with_directives(
            &DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: Ident::create_local("a"),
                        value: Some(Expression::var(Ident::create_local("Belt_Array"))),
                        property: crate::lambda::compat::LetKind::Strict,
                        ident_info: Default::default(),
                    })],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            None,
            &[
                "first directive;".to_string(),
                "second directive;".to_string(),
            ],
            false,
        );

        assert!(rendered.starts_with(
            "first directive;\nsecond directive;\n// Generated by ReScript, PLEASE EDIT WITH CARE\n"
        ));
    }

    #[test]
    fn test_print_deps_program_keeps_blank_line_after_imports() {
        let import_id = Ident::create_local("Js_dict");
        let resolver = ModulePathResolver::from_compile_options(
            None,
            Some(Path::new("/tmp/DictInference.mjs")),
            None,
            None,
        );
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: Ident::create_local("dict"),
                        value: Some(Expression::new(ExpressionDesc::Object(None, vec![]))),
                        property: crate::lambda::compat::LetKind::Strict,
                        ident_info: Default::default(),
                    })],
                    vec![],
                ),
                modules: vec![ModuleId {
                    id: import_id,
                    kind: Kind::External {
                        name: "@rescript/runtime/lib/es6/Js_dict.js".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                }],
                side_effect: Some(String::new()),
            },
            Some(&resolver),
        );

        assert!(rendered.contains(
            "import * as Js_dict from \"@rescript/runtime/lib/es6/Js_dict.js\";\n\nlet dict = {};"
        ));
    }

    #[test]
    fn test_print_deps_program_scopes_module_import_aliases_across_runtime_and_external_modules() {
        let runtime = ModuleId {
            id: Ident::create_persistent("List"),
            kind: Kind::Runtime,
            dynamic_import: false,
        };
        let react_v = ModuleId {
            id: Ident::create_local("List"),
            kind: Kind::External {
                name: "reactV".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let react_x = ModuleId {
            id: Ident::create_local("List"),
            kind: Kind::External {
                name: "reactX".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let resolver = ModulePathResolver::from_compile_options(
            None,
            Some(Path::new("/tmp/module_aliases.mjs")),
            None,
            None,
        );
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: Ident::create_local("runtimeMember"),
                            value: Some(Expression::qualified(
                                runtime.clone(),
                                Some("map".to_string()),
                            )),
                            property: crate::lambda::compat::LetKind::Strict,
                            ident_info: Default::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: Ident::create_local("reactVMember"),
                            value: Some(Expression::qualified(
                                react_v.clone(),
                                Some("ff".to_string()),
                            )),
                            property: crate::lambda::compat::LetKind::Strict,
                            ident_info: Default::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: Ident::create_local("reactXMember"),
                            value: Some(Expression::qualified(
                                react_x.clone(),
                                Some("ff2".to_string()),
                            )),
                            property: crate::lambda::compat::LetKind::Strict,
                            ident_info: Default::default(),
                        }),
                    ],
                    vec![],
                ),
                modules: vec![runtime, react_v, react_x],
                side_effect: Some(String::new()),
            },
            Some(&resolver),
        );

        assert!(rendered.contains("import * as List from \"@rescript/runtime/lib/es6/List.js\";"));
        assert!(rendered.contains("import * as List$1 from \"reactV\";"));
        assert!(rendered.contains("import * as List$2 from \"reactX\";"));
        assert!(rendered.contains("let runtimeMember = List.map;"));
        assert!(rendered.contains("let reactVMember = List$1.ff;"));
        assert!(rendered.contains("let reactXMember = List$2.ff2;"));
    }

    #[test]
    fn test_print_deps_program_preserves_all_import_attributes() {
        let import_id = Ident::create_local("MyJsonJson");
        let resolver = ModulePathResolver::from_compile_options(
            None,
            Some(Path::new("/tmp/ImportAttributes.mjs")),
            None,
            None,
        );
        let mut printer = JsPrinter::with_module_path_resolver(Some(&resolver));
        let printed = printer.print_module_imports(&[ModuleId {
            id: import_id,
            kind: Kind::External {
                name: "./myJson.json".to_string(),
                default: true,
                import_attributes: Some(ImportAttributes {
                    entries: vec![
                        ("type".to_string(), "json".to_string()),
                        ("some-identifier".to_string(), "yep".to_string()),
                    ],
                }),
            },
            dynamic_import: false,
        }]);

        assert!(printed);
        assert_eq!(
            printer.into_output(),
            "import MyJsonJson from \"./myJson.json\" with {\"type\": \"json\", \"some-identifier\": \"yep\"};"
        );
    }

    #[test]
    fn test_print_deps_program_keeps_header_spacing_without_imports() {
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: Ident::create_local("x"),
                        value: Some(Expression::number(Number::int(1))),
                        property: crate::lambda::compat::LetKind::Strict,
                        ident_info: Default::default(),
                    })],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            None,
        );

        assert!(
            rendered.starts_with("// Generated by ReScript, PLEASE EDIT WITH CARE\n\n\nlet x = 1;")
        );
    }

    #[test]
    fn test_print_deps_program_omits_undefined_initializer() {
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: Ident::create_local("VS"),
                        value: Some(Expression::undefined(false)),
                        property: crate::lambda::compat::LetKind::Strict,
                        ident_info: Default::default(),
                    })],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            None,
        );

        assert!(rendered.contains("\n\n\nlet VS;\n"));
    }

    #[test]
    fn test_print_deps_program_keeps_blank_line_before_purity_trailer_without_exports() {
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(vec![Statement::debugger()], vec![]),
                modules: vec![],
                side_effect: Some(String::new()),
            },
            None,
        );

        assert!(rendered.contains("debugger;\n\n/*  Not a pure module */"));
    }

    #[test]
    fn test_print_deps_program_aliases_default_export_name() {
        let default_ident = Ident::create_local("default");
        let rendered = print_deps_program(
            &DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: default_ident.clone(),
                        value: Some(Expression::string("xx")),
                        property: crate::lambda::compat::LetKind::Strict,
                        ident_info: Default::default(),
                    })],
                    vec![default_ident],
                ),
                modules: vec![],
                side_effect: None,
            },
            None,
        );

        assert!(rendered.contains("export {\n  $$default as default,\n}"));
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
            property: crate::lambda::compat::LetKind::Strict,
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
            property: crate::lambda::compat::LetKind::Strict,
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
