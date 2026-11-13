//! The deliberately partial structural equality used by J normalisation.
use crate::bir::{Bir, Constant, JsPayload, NodeId, View};

/// B:237 ocaml_eq_expression / B:217 ocaml_eq_block, with an explicit stack.
/// Unsupported kinds compare false even against themselves. Stops at the first
/// mismatch. There is no legacy depth cap: cost is O(paired nodes + compared
/// literal bytes), bounded by the smaller input tree; stack is O(tree width +
/// depth). `steps` counts inspected pairs, including the mismatching pair.
pub fn equal(b: &Bir, left: NodeId, right: NodeId, steps: &mut usize) -> bool {
    let mut work = b.j_equal_work.borrow_mut();
    work.clear();
    work.push((left, right));
    while let Some((l, r)) = work.pop() {
        *steps += 1;
        let (la, ra) = (b.node(l).aux(), b.node(r).aux());
        let same = match (b.view(l), b.view(r)) {
            (View::JNull, View::JNull) | (View::SDebugger, View::SDebugger) => true,
            (View::JUndefined, View::JUndefined) | (View::JBool, View::JBool) => {
                (la != 0) == (ra != 0)
            }
            (View::Var { var: x }, View::Var { var: y }) => {
                b.vars.j_origin[x.index()] == b.vars.j_origin[y.index()]
            },
            (
                View::JQualified {
                    module: x,
                    member: xm,
                },
                View::JQualified {
                    module: y,
                    member: ym,
                },
            ) => {
                let (x, y) = (&b.pools.j_modules[x.index()], &b.pools.j_modules[y.index()]);
                let kind = match (&x.kind, &y.kind) {
                    (crate::js_ir::Kind::Ml, crate::js_ir::Kind::Ml)
                    | (crate::js_ir::Kind::Runtime, crate::js_ir::Kind::Runtime) => true,
                    (
                        crate::js_ir::Kind::External { name: x, .. },
                        crate::js_ir::Kind::External { name: y, .. },
                    ) => x == y,
                    _ => false,
                };
                x.id.same(&y.id) && kind && xm == ym
            }
            (View::JNumber { value: x }, View::JNumber { value: y }) => {
                match (b.constant(x), b.constant(y)) {
                    (Constant::Int(x), Constant::Int(y)) => x == y,
                    (Constant::Char(x), Constant::Char(y)) => x == y,
                    (Constant::Int(x), Constant::Char(y))
                    | (Constant::Char(y), Constant::Int(x)) => *x == i64::from(*y),
                    (Constant::BigInt(x), Constant::BigInt(y)) => x == y,
                    _ => false,
                }
            }
            (View::JStr { text: x }, View::JStr { text: y }) => x == y,
            (View::JTemplate { info: x, .. }, View::JTemplate { info: y, .. })
                if la == 1 && ra == 1 =>
            {
                match (b.javascript(x), b.javascript(y)) {
                    (JsPayload::Template(x), JsPayload::Template(y)) => {
                        x.len() == y.len()
                            && x.iter()
                                .zip(y)
                                .all(|(x, y)| x.raw == y.raw && x.cooked == y.cooked)
                    }
                    _ => false,
                }
            }
            (
                View::JDot {
                    object: x,
                    property: xp,
                    position: xi,
                },
                View::JDot {
                    object: y,
                    property: yp,
                    position: yi,
                },
            ) if la == 0 && ra == 0 => {
                work.push((x, y));
                xp == yp && xi == yi
            }
            (
                View::JIndex {
                    object: x,
                    index: xi,
                },
                View::JIndex {
                    object: y,
                    index: yi,
                },
            ) => {
                work.push((xi, yi));
                work.push((x, y));
                true
            }
            (View::JBin { left: x, right: xr }, View::JBin { left: y, right: yr }) => {
                work.push((xr, yr));
                work.push((x, y));
                la == ra
            }
            (
                View::JSeq {
                    first: x,
                    second: xr,
                },
                View::JSeq {
                    first: y,
                    second: yr,
                },
            ) => {
                work.push((xr, yr));
                work.push((x, y));
                true
            }
            (View::JOptional { value: x }, View::JOptional { value: y }) => {
                work.push((x, y));
                (la != 0) == (ra != 0)
            }
            (
                View::JCall {
                    callee: x,
                    args: xs,
                    ..
                },
                View::JCall {
                    callee: y,
                    args: ys,
                    ..
                },
            ) => {
                work.extend(xs.iter().copied().zip(ys.iter().copied()).rev());
                work.push((x, y));
                xs.len() == ys.len()
            }
            (
                View::JBlockLit {
                    values: xs,
                    info: x,
                },
                View::JBlockLit {
                    values: ys,
                    info: y,
                },
            ) => {
                work.extend(xs.iter().copied().zip(ys.iter().copied()).rev());
                la == ra
                    && xs.len() == ys.len()
                    && b.block_tag(x) == b.block_tag(y)
            }
            (View::SExp { value: x }, View::SExp { value: y })
            | (View::SReturn { value: x }, View::SReturn { value: y }) => {
                work.push((x, y));
                true
            }
            (View::SBreak { label: x }, View::SBreak { label: y }) => x == y,
            (View::SBlock { statements: xs }, View::SBlock { statements: ys }) => {
                work.extend(xs.iter().copied().zip(ys.iter().copied()).rev());
                xs.len() == ys.len()
            }
            _ => false,
        };
        if !same {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::name::Name;

    #[test]
    fn ten_thousand_variable_origins_take_one_pair_step_each() {
        let mut b = Bir::default();
        let mut steps = 0;
        for i in 0..10_000 {
            let original = b.new_var_id(Name::new("x"), 2 * i);
            let copy = b.new_var_id(Name::new("x"), 2 * i + 1);
            b.vars.j_origin[copy.index()] = original;
            let left = b.new_node(View::Var { var: original }, 0);
            let right = b.new_node(View::Var { var: copy }, 0);
            assert!(equal(&b, left, right, &mut steps));
            b.release(left);
            b.release(right);
        }
        assert_eq!(steps, 10_000); // two direct origin-table reads per pair
        assert_eq!(b.vars.j_origin.len(), 20_000);
        b.validate(None).unwrap();
    }
}
