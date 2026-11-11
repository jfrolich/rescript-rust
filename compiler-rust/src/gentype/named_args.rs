// Port of compiler/gentype/NamedArgs.ml:1-14.

use crate::gentype::gen_type_common::{ArgType, Label, Type};

/// `NamedArgs.group`: the arguments of a function type, optional ones
/// wrapped in an option type. A function taking only `unit` has none.
pub fn group(labeled_types: Vec<(Label, Type)>) -> Vec<ArgType> {
    // Mirrors compiler/gentype/NamedArgs.ml:3-14.
    let types = labeled_types
        .into_iter()
        .map(|(lbl, a_type)| match lbl {
            Label::Nolabel => ArgType {
                a_name: String::new(),
                a_type,
            },
            Label::Label(lbl) => ArgType {
                a_name: lbl,
                a_type,
            },
            Label::OptLabel(lbl) => ArgType {
                a_name: lbl,
                a_type: Type::Option(Box::new(a_type)),
            },
        })
        .collect::<Vec<_>>();
    match types.as_slice() {
        [ArgType { a_type, .. }] if *a_type == crate::gentype::gen_type_common::unit_t() => vec![],
        _ => types,
    }
}
