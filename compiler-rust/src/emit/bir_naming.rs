//! One iterative traversal records print-order name requests and exact free
//! environments together. Scope name choice consumes that linear schedule,
//! never traversing the input again. All identifier-indexed state is dense.
use super::{
    Unsupported,
    view::{NameKey, NameSource, PrintedNames, View},
    walk,
};
use crate::bir::emit_view::EmitterView;
use crate::js_ir::printer::convert_ident_atom;
use crate::js_ir::{
    ModulePathResolver,
    arena::{Expr, ExprKind, FunId, Stmt, StmtKind},
};
use crate::name::Name;
use ahash::{AHashMap as Map, AHashSet as Set};

#[derive(Clone, Copy)]
enum Print {
    Yes,
    No,
    Expr(Expr),
    Stmt(Stmt, Option<bool>),
}
impl Print {
    fn yes(self) -> bool {
        matches!(self, Self::Yes)
    }
}
#[derive(Clone, Copy)]
enum Event {
    Name(usize, bool),
    Scope(usize, Option<usize>),
    Finish(Stmt, usize),
}
#[derive(Default)]
struct Plan {
    events: Vec<Event>,
    requested: Set<(usize, bool)>,
    defined: Set<usize>,
    used: Set<usize>,
    free: Vec<usize>,
    function: Option<FunId>,
    form: Option<walk::FunctionForm>,
}
impl Plan {
    fn request(&mut self, var: usize, module: bool) {
        if self.requested.insert((var, module)) {
            self.events.push(Event::Name(var, module));
        }
    }
}
enum Task {
    Expr(Expr, Print, Option<(usize, bool)>),
    Stmt(Stmt, Print, bool, Option<bool>),
    Bind(usize, Print),
    Finish(Stmt, usize, Print),
    Close(usize),
}
#[derive(Default, Clone)]
struct Group {
    next: usize,
    stamps: im_rc::HashMap<i32, Name>,
    used: im_rc::HashSet<Name>,
}
#[derive(Default)]
struct Scope {
    groups: Map<Name, Group>,
    assigned: Vec<usize>,
    previous: Vec<(Name, Option<usize>)>,
}

pub(super) struct Names {
    printed: Vec<Option<Name>>,
    visible: Vec<Option<Name>>,
    finishes: Vec<Option<Name>>,
    method_this: Vec<bool>,
    scopes: Vec<Scope>,
    visible_groups: Map<Name, usize>,
    converted: Map<Name, Name>,
    raw: Set<Name>,
    finish_count: usize,
    pub(super) steps: usize,
}
impl Names {
    pub(super) fn collect(
        a: &EmitterView<'_>,
        block: &[Stmt],
        resolver: &ModulePathResolver,
        jsx: bool,
    ) -> Result<Self, Unsupported> {
        let mut this = Self {
            printed: vec![None; a.identities().len()],
            visible: vec![None; a.identities().len()],
            finishes: vec![None; a.node_capacity()],
            method_this: vec![false; a.node_capacity()],
            scopes: vec![Scope::default()],
            visible_groups: Map::new(),
            converted: Map::new(),
            raw: a
                .identities()
                .iter()
                .take(a.syntax_variable_count())
                .filter(|id| crate::js_ir::arena::is_raw_js_name(id))
                .map(|id| id.name_atom())
                .collect(),
            finish_count: 0,
            steps: 0,
        };
        let mut plans = vec![Plan::default()];
        let mut scope = 0;
        let mut tasks = Vec::new();
        Self::block_tasks(a, block, Print::Yes, true, None, false, &mut tasks);
        while let Some(task) = tasks.pop() {
            this.steps += 1;
            match task {
                Task::Close(parent) => {
                    let p = &mut plans[scope];
                    p.used.retain(|v| !p.defined.contains(v));
                    if let Some(f) = p.function {
                        let h = a.fun(f);
                        if h.is_method && !a.ident_slice(h.params).is_empty() {
                            let v = a.name_key(NameSource::Parameter(h.params, 0)).slot;
                            this.method_this[f.index()] = p.used.remove(&v);
                        }
                    }
                    p.free = p.used.drain().collect();
                    let mut comparisons = 0;
                    p.free.sort_unstable_by(|left, right| {
                        comparisons += 1;
                        a.identities()[*left].cmp(&a.identities()[*right])
                    });
                    this.steps += comparisons;
                    this.steps += p.free.len() + p.defined.len();
                    let free = std::mem::take(&mut p.free);
                    plans[parent].used.extend(free.iter().copied());
                    plans[scope].free = free;
                    scope = parent;
                }
                Task::Bind(v, print) => {
                    plans[scope].defined.insert(v);
                    if print.yes() {
                        plans[scope].request(v, false);
                    }
                }
                Task::Finish(s, v, print) => {
                    if print.yes() {
                        plans[scope].events.push(Event::Finish(s, v));
                    }
                }
                Task::Expr(e, mut print, binding) => {
                    if matches!(print, Print::Expr(target) if target == e) {
                        print = Print::Yes;
                    }
                    walk::expression_comment(a, e)?;
                    match a.ek(e) {
                        ExprKind::Var(id) => {
                            let v = a.name_key(NameSource::Variable(id)).slot;
                            if !plans[scope].defined.contains(&v) {
                                plans[scope].used.insert(v);
                            }
                            if print.yes() {
                                plans[scope].request(v, false);
                            }
                        }
                        ExprKind::Qualified(id) => {
                            let v = a.name_key(NameSource::Qualified(id)).slot;
                            if !plans[scope].defined.contains(&v) {
                                plans[scope].used.insert(v);
                            }
                            if print.yes() {
                                plans[scope].request(v, true);
                            }
                        }
                        ExprKind::Fun(f) => {
                            let child = plans.len();
                            let h = a.fun(f);
                            let form = walk::function_form(
                                a,
                                f,
                                binding.is_some_and(|(_, top)| top) && print.yes(),
                            )?;
                            if print.yes() {
                                plans[scope]
                                    .events
                                    .push(Event::Scope(child, binding.map(|(slot, _)| slot)));
                            }
                            let mut plan = Plan {
                                function: Some(f),
                                form: Some(form),
                                ..Plan::default()
                            };
                            for i in usize::from(h.is_method)..a.ident_slice(h.params).len() {
                                plan.defined
                                    .insert(a.name_key(NameSource::Parameter(h.params, i)).slot);
                            }
                            plans.push(plan);
                            tasks.push(Task::Close(scope));
                            scope = child;
                            let body_print = if !print.yes() {
                                Print::No
                            } else {
                                match form {
                                    walk::FunctionForm::Eta(e)
                                    | walk::FunctionForm::ArrowExpression(e) => Print::Expr(e),
                                    walk::FunctionForm::ArrowEmpty => Print::No,
                                    walk::FunctionForm::Declaration
                                    | walk::FunctionForm::ArrowBlock
                                    | walk::FunctionForm::Method => Print::Yes,
                                }
                            };
                            Self::block_tasks(
                                a,
                                &a.stmts(h.body),
                                body_print,
                                false,
                                Some(h.return_unit),
                                true,
                                &mut tasks,
                            );
                        }
                        ExprKind::StringAppend(l, r) => {
                            tasks.push(Task::Expr(r, print, None));
                            tasks.push(Task::Expr(l, print, None));
                        }
                        ExprKind::CamlBlock(items, _, tag) => {
                            let items = a.exprs(items);
                            let tag = a.tag(tag);
                            walk::block_supported(&items, tag)?;
                            let mut children: Vec<_> = walk::block_elements(a, &items, tag)
                                .map(|(_, e)| (e, print))
                                .collect();
                            if matches!(tag, crate::lambda::TagInfo::PolyVar(_)) {
                                children.extend(items.iter().skip(2).map(|e| (*e, Print::No)));
                            }
                            tasks.extend(
                                children
                                    .into_iter()
                                    .rev()
                                    .map(|(e, p)| Task::Expr(e, p, None)),
                            );
                        }
                        _ => {
                            let mut children = Vec::new();
                            walk::expression_children(a, e, jsx, |e| {
                                children.push(e);
                                Ok(())
                            })?;
                            tasks.extend(
                                children
                                    .into_iter()
                                    .rev()
                                    .map(|e| Task::Expr(e, print, None)),
                            );
                        }
                    }
                }
                Task::Stmt(s, mut print, top, mut tail) => {
                    if let Print::Stmt(target, selected_tail) = print {
                        if target == s {
                            print = Print::Yes;
                            tail = selected_tail;
                        }
                    }
                    match a.sk(s) {
                        StmtKind::Block(b) => {
                            Self::block_tasks(a, &a.stmts(b), print, false, None, false, &mut tasks)
                        }
                        StmtKind::Variable(v) => {
                            let d = a.var(v);
                            let slot = a.name_key(NameSource::Declaration(v)).slot;
                            let mut fields = Vec::new();
                            if let Some((rest, _)) = walk::rest_declaration(a, &d) {
                                for (i, field) in a.rest(rest).iter().enumerate() {
                                    if field.ident.is_some() {
                                        fields.push(a.name_key(NameSource::Rest(rest, i)).slot);
                                    }
                                }
                            }
                            plans[scope].defined.extend(fields.iter().copied());
                            plans[scope].defined.insert(slot);
                            let mut value_print = print;
                            let mut bind = None;
                            if print.yes() {
                                match walk::prints_declaration(&d) {
                                    walk::Declaration::Omit => value_print = Print::No,
                                    walk::Declaration::Effect(e) => {
                                        if walk::omitted_expression(a, e) {
                                            value_print = Print::No;
                                        }
                                    }
                                    walk::Declaration::Binding => {
                                        if d.value
                                            .is_some_and(|e| matches!(a.ek(e), ExprKind::Fun(_)))
                                        {
                                            bind = Some((slot, top));
                                        } else {
                                            for v in fields {
                                                plans[scope].request(v, false);
                                            }
                                            plans[scope].request(slot, false);
                                            if d.value.is_some_and(|e| walk::undefined(a, e)) {
                                                value_print = Print::No;
                                            }
                                        }
                                    }
                                }
                            }
                            if let Some(e) = d.value {
                                tasks.push(Task::Expr(e, value_print, bind));
                            }
                        }
                        StmtKind::Exp(e) => {
                            let p = if print.yes() && walk::omitted_expression(a, e) {
                                Print::No
                            } else {
                                print
                            };
                            tasks.push(Task::Expr(e, p, None));
                        }
                        StmtKind::Return(e) => {
                            let p = if !print.yes() {
                                print
                            } else if tail == Some(true) {
                                walk::tail_effect(a, e).map_or(Print::No, Print::Expr)
                            } else if walk::undefined(a, e) {
                                Print::No
                            } else {
                                Print::Yes
                            };
                            tasks.push(Task::Expr(e, p, None));
                        }
                        StmtKind::If(c, t, f) => {
                            let fbody = a.stmts(f);
                            let fp = if !print.yes() {
                                print
                            } else if walk::else_omitted(a, &fbody)
                                || (tail.is_some()
                                    && matches!(&*fbody,[s] if walk::return_undefined(a,*s)))
                            {
                                Print::No
                            } else if let Some(s) = walk::else_if(a, &fbody) {
                                Print::Stmt(s, tail)
                            } else {
                                Print::Yes
                            };
                            Self::block_tasks(a, &fbody, fp, false, None, false, &mut tasks);
                            Self::block_tasks(
                                a,
                                &a.stmts(t),
                                print,
                                false,
                                None,
                                false,
                                &mut tasks,
                            );
                            tasks.push(Task::Expr(c, print, None));
                        }
                        StmtKind::Debugger => {}
                        _ => {
                            let binder = match a.sk(s) {
                                StmtKind::ForRange(id) => Some(a.for_range(id).ident),
                                StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
                                    Some(a.for_of(id).ident)
                                }
                                StmtKind::Try(id) => a.try_info(id).catch.map(|(id, _)| id),
                                _ => None,
                            };
                            let mut children = Vec::new();
                            walk::statement_children(a, s, |child| {
                                children.push(child);
                                Ok(())
                            })?;
                            for child in children.into_iter().rev() {
                                match child {
                                    walk::StatementChild::Binder(_) => tasks.push(Task::Bind(
                                        a.name_key(NameSource::Variable(binder.expect("binder")))
                                            .slot,
                                        print,
                                    )),
                                    walk::StatementChild::Finish(s) => tasks.push(Task::Finish(
                                        s,
                                        a.name_key(NameSource::Variable(
                                            binder.expect("range binder"),
                                        ))
                                        .slot,
                                        print,
                                    )),
                                    walk::StatementChild::Expression(e) => {
                                        tasks.push(Task::Expr(e, print, None))
                                    }
                                    walk::StatementChild::Block(b) => Self::block_tasks(
                                        a,
                                        &a.stmts(b),
                                        print,
                                        false,
                                        None,
                                        false,
                                        &mut tasks,
                                    ),
                                }
                            }
                        }
                    }
                }
            }
        }
        for (i, m) in a.modules().iter().enumerate() {
            if !m.dynamic_import && resolver.resolve_module_path(m).is_some() {
                this.add(a, a.name_key(NameSource::Import(i, m.id)).slot, true)?;
            }
        }
        for v in a.reservation_slots() {
            this.reserve(a, &[v])?;
        }
        enum Choice {
            Event(Event),
            Leave,
        }
        let mut choices: Vec<_> = plans[0]
            .events
            .iter()
            .rev()
            .copied()
            .map(Choice::Event)
            .collect();
        while let Some(choice) = choices.pop() {
            this.steps += 1;
            match choice {
                Choice::Leave => this.leave(),
                Choice::Event(Event::Name(v, module)) => this.add(a, v, module)?,
                Choice::Event(Event::Finish(s, v)) => {
                    let base = this.base(a, v);
                    let stamp = -1 - this.finish_count as i32;
                    let name = this.assign(Name::new(&format!("{base}_finish")), stamp);
                    if this.finishes[s.index()].is_none() {
                        this.finish_count += 1;
                    }
                    if this.finishes[s.index()]
                        .replace(name)
                        .is_some_and(|old| old != name)
                    {
                        return Err(Unsupported(
                            "range finish spelling differs between occurrences",
                        ));
                    }
                }
                Choice::Event(Event::Scope(index, binding)) => {
                    let p = &plans[index];
                    let f = p.function.unwrap();
                    let eta = matches!(p.form, Some(walk::FunctionForm::Eta(_)));
                    if eta && let Some(v) = binding {
                        this.add(a, v, false)?;
                    }
                    let mut env = p.free.clone();
                    if let Some(v) = binding
                        && let Err(pos) =
                            env.binary_search_by_key(&a.identities()[v], |v| a.identities()[*v])
                    {
                        env.insert(pos, v);
                    }
                    this.reserve(a, &env)?;
                    if let Some(v) = binding {
                        this.add(a, v, false)?;
                    }
                    this.enter(a, &env);
                    let h = a.fun(f);
                    if !eta {
                        for i in 0..a.ident_slice(h.params).len() {
                            if h.is_method && i == 0 && !this.method_this[f.index()] {
                                continue;
                            }
                            this.add(
                                a,
                                a.name_key(NameSource::Parameter(h.params, i)).slot,
                                false,
                            )?;
                        }
                    }
                    choices.push(Choice::Leave);
                    choices.extend(p.events.iter().rev().copied().map(Choice::Event));
                }
            }
        }
        for (i, id) in a.exports().iter().enumerate() {
            this.add(a, a.name_key(NameSource::Export(i, *id)).slot, false)?;
        }
        Ok(this)
    }
    fn block_tasks(
        a: &EmitterView<'_>,
        block: &[Stmt],
        print: Print,
        top: bool,
        tail: Option<bool>,
        function: bool,
        tasks: &mut Vec<Task>,
    ) {
        let len =
            if function && block.len() >= 2 && walk::return_undefined(a, block[block.len() - 1]) {
                block.len() - 1
            } else {
                block.len()
            };
        for (i, s) in block.iter().enumerate().rev() {
            let p = if print.yes() && i >= len {
                Print::No
            } else {
                print
            };
            tasks.push(Task::Stmt(
                *s,
                p,
                top,
                if i + 1 == len { tail } else { None },
            ));
        }
    }
    fn base(&mut self, a: &EmitterView<'_>, v: usize) -> Name {
        let name = a.identities()[v].name_atom();
        *self
            .converted
            .entry(name)
            .or_insert_with(|| convert_ident_atom(name))
    }
    fn used(&self, name: Name) -> bool {
        let groups = &self.scopes.last().unwrap().groups;
        if groups.get(&name).is_some_and(|g| g.used.contains(&name)) {
            return true;
        }
        if let Some((base, suffix)) = name.rsplit_once('$')
            && suffix.starts_with(|c: char| ('1'..='9').contains(&c))
            && suffix.bytes().all(|c| c.is_ascii_digit())
        {
            return groups
                .get(&Name::new(base))
                .is_some_and(|g| g.used.contains(&name));
        }
        false
    }
    fn assign(&mut self, base: Name, stamp: i32) -> Name {
        self.steps += 1;
        if let Some(n) = self
            .scopes
            .last()
            .unwrap()
            .groups
            .get(&base)
            .and_then(|g| g.stamps.get(&stamp))
        {
            return *n;
        }
        let mut next = self
            .scopes
            .last()
            .unwrap()
            .groups
            .get(&base)
            .map_or(0, |g| g.next);
        let name = loop {
            self.steps += 1;
            let name = if next == 0 {
                base
            } else {
                Name::new(&format!("{base}${next}"))
            };
            if !self.used(name) && !(next > 0 && self.raw.contains(&name)) {
                break name;
            }
            next += 1;
        };
        let index = self.scopes.len() - 1;
        if !self.scopes[index].groups.contains_key(&base) {
            let old = self.visible_groups.insert(base, index);
            self.scopes[index].previous.push((base, old));
        }
        let group = self.scopes[index].groups.entry(base).or_default();
        group.next = next + 1;
        group.stamps.insert(stamp, name);
        group.used.insert(name);
        name
    }
    fn add(&mut self, a: &EmitterView<'_>, v: usize, module: bool) -> Result<(), Unsupported> {
        self.steps += 1;
        let id = a.identities()[v];
        let name = if let Some(name) = self.visible[v] {
            name
        } else if id.stamp() == 0 && !module {
            id.name_atom()
        } else {
            let base = self.base(a, v);
            let name = self.assign(base, id.stamp());
            self.visible[v] = Some(name);
            self.scopes.last_mut().unwrap().assigned.push(v);
            name
        };
        if self.printed[v].replace(name).is_some_and(|old| old != name) {
            return Err(Unsupported(
                "identifier spelling differs between sibling scopes",
            ));
        }
        Ok(())
    }
    fn reserve(&mut self, a: &EmitterView<'_>, ids: &[usize]) -> Result<(), Unsupported> {
        for &v in ids {
            self.steps += 1;
            if a.identities()[v].stamp() == 0 {
                let base = self.base(a, v);
                self.assign(base, 0);
            } else {
                self.add(a, v, false)?;
            }
        }
        Ok(())
    }
    fn enter(&mut self, a: &EmitterView<'_>, ids: &[usize]) {
        let mut scope = Scope::default();
        for &v in ids {
            self.steps += 1;
            let base = self.base(a, v);
            if scope.groups.contains_key(&base) {
                continue;
            }
            let parent = self.visible_groups[&base];
            scope
                .groups
                .insert(base, self.scopes[parent].groups[&base].clone());
        }
        for base in scope.groups.keys() {
            let old = self.visible_groups.insert(*base, self.scopes.len());
            scope.previous.push((*base, old));
        }
        self.scopes.push(scope);
    }
    fn leave(&mut self) {
        let scope = self.scopes.pop().unwrap();
        for v in scope.assigned {
            self.visible[v] = None;
        }
        for (base, old) in scope.previous {
            if let Some(i) = old {
                self.visible_groups.insert(base, i);
            } else {
                self.visible_groups.remove(&base);
            }
        }
    }
}
impl PrintedNames for Names {
    fn name(&self, key: NameKey) -> &str {
        self.printed[key.slot]
            .as_ref()
            .expect("name assigned before construction")
    }
    fn method_this_used(&self, f: FunId) -> bool {
        self.method_this[f.index()]
    }
    fn finish(&self, s: Stmt) -> &str {
        self.finishes[s.index()].as_ref().expect("finish assigned")
    }
    fn raw_prefix_len(&self) -> usize {
        self.printed
            .iter()
            .chain(&self.finishes)
            .flatten()
            .filter(|n| n.starts_with(super::raw::PREFIX))
            .map(|n| n.len() + 1)
            .max()
            .unwrap_or(super::raw::PREFIX.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::bridge_j;
    use crate::ident::{Ident, IdentFlags};
    use crate::js_ir::{IdentInfo, Property, arena::*};

    fn resolver() -> ModulePathResolver {
        ModulePathResolver::from_compile_options(None, None, None, None, None, None, false)
    }
    fn program(arena: JsArena, block: Vec<Stmt>) -> JsDepsProgram {
        JsDepsProgram {
            program: JsProgram::new_in(block, vec![], arena),
            modules: vec![],
            side_effect: None,
        }
    }
    fn function(a: &mut JsArena, body: Vec<Stmt>) -> Expr {
        let params = a.ident_list(&[]);
        let body = a.stmt_list(&body);
        let f = a.fun_id(FunInfo {
            is_method: false,
            params,
            body,
            return_unit: false,
            async_: false,
            directive: None,
        });
        a.expr(ExprKind::Fun(f))
    }
    fn collect(p: &JsDepsProgram) -> Names {
        let imported = bridge_j::import_js(p).unwrap();
        let view = EmitterView::new(&imported).unwrap();
        Names::collect(&view, &view.root(), &resolver(), false).unwrap()
    }
    fn wide(n: usize) -> Names {
        let mut a = JsArena::new();
        let mut body = Vec::new();
        for i in 0..n {
            let id = Ident::new("x", i as i32 + 1, IdentFlags::NONE);
            let value = a.expr(ExprKind::Null);
            let v = a.var_id(VarDecl {
                ident: id,
                value: Some(value),
                property: Property::Strict,
                ident_info: IdentInfo::default(),
            });
            body.push(a.stmt(StmtKind::Variable(v)));
        }
        let f = function(&mut a, body);
        let s = a.stmt(StmtKind::Exp(f));
        collect(&program(a, vec![s]))
    }
    fn deep(n: usize) -> Names {
        let mut a = JsArena::new();
        let outer = a.ident_id(Ident::new("outer", 1, IdentFlags::NONE));
        let mut value = a.expr(ExprKind::Null);
        for _ in 0..n {
            // Every function directly captures the same outer variable, and
            // also contains the preceding function. No host recursion is used.
            let capture = a.expr(ExprKind::Var(outer));
            let use_ = a.stmt(StmtKind::Return(capture));
            let nested = a.stmt(StmtKind::Exp(value));
            value = function(&mut a, vec![nested, use_]);
        }
        let s = a.stmt(StmtKind::Exp(value));
        collect(&program(a, vec![s]))
    }
    #[test]
    fn ten_thousand_variables_in_one_function_are_linear() {
        let small = wide(5_000);
        let large = wide(10_000);
        assert!(
            large.steps <= 2 * small.steps + 100,
            "{} -> {}",
            small.steps,
            large.steps
        );
        assert!(large.steps < 30 * 10_000);
        assert_eq!(large.printed.iter().flatten().count(), 10_000);
        // Uses address the VarId slot, not the source identifier or its hash.
        let key = NameKey {
            slot: 0,
            ident: Ident::new("irrelevant", 999_999, IdentFlags::NONE),
        };
        assert_eq!(large.name(key), "x");
    }
    #[test]
    fn ten_thousand_nested_capturing_functions_are_linear() {
        let small = deep(5_000);
        let large = deep(10_000);
        assert!(
            large.steps <= 2 * small.steps + 100,
            "{} -> {}",
            small.steps,
            large.steps
        );
        assert!(large.steps < 40 * 10_000);
        assert_eq!(large.printed.iter().flatten().count(), 1);
    }
}
