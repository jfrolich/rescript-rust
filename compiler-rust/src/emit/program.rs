use super::Unsupported;
use crate::js_ir::{ModulePathResolver, arena::JsDepsProgram};

pub(super) fn emit(
    _program: &JsDepsProgram,
    _resolver: &ModulePathResolver,
    _directives: &[String],
    _debug: bool,
    _jsx_preserve: bool,
    _header: bool,
) -> Result<(String, Option<String>), Unsupported> {
    Err(Unsupported("program"))
}
