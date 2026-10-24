// Port of compiler/gentype/Emitters.ml:1-52 and Emitters.mli:1-9.

/// Each emitter holds its chunks in emission order. OCaml conses onto a
/// list and reverses in `to_string`; pushing gives the same output order.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct T {
    pub require_emitter_early: Vec<String>,
    pub export_emitter_early: Vec<String>,
    pub require_emitter: Vec<String>,
    pub import_emitter: Vec<String>,
    pub export_emitter: Vec<String>,
}

pub fn initial() -> T {
    // Mirrors compiler/gentype/Emitters.ml:9-16.
    T {
        require_emitter_early: Vec::new(),
        export_emitter_early: Vec::new(),
        require_emitter: Vec::new(),
        import_emitter: Vec::new(),
        export_emitter: Vec::new(),
    }
}

pub fn string(mut emitter: Vec<String>, s: String) -> Vec<String> {
    // Mirrors compiler/gentype/Emitters.ml:18.
    emitter.push(s);
    emitter
}

pub fn require_early(mut emitters: T, s: String) -> T {
    // Mirrors compiler/gentype/Emitters.ml:20-24.
    emitters.require_emitter_early = string(emitters.require_emitter_early, s);
    emitters
}

pub fn export_early(mut emitters: T, s: String) -> T {
    // Mirrors compiler/gentype/Emitters.ml:26-30.
    emitters.export_emitter_early = string(emitters.export_emitter_early, s);
    emitters
}

pub fn require(mut emitters: T, s: String) -> T {
    // Mirrors compiler/gentype/Emitters.ml:32-36.
    emitters.require_emitter = string(emitters.require_emitter, s);
    emitters
}

pub fn import(mut emitters: T, s: String) -> T {
    // Mirrors compiler/gentype/Emitters.ml:38-39.
    emitters.import_emitter = string(emitters.import_emitter, s);
    emitters
}

pub fn export(mut emitters: T, s: String) -> T {
    // Mirrors compiler/gentype/Emitters.ml:41-42.
    emitters.export_emitter = string(emitters.export_emitter, s);
    emitters
}

pub fn to_string(separator: &str, emitters: T) -> String {
    // Mirrors compiler/gentype/Emitters.ml:44-52.
    let mut chunks = emitters.require_emitter_early;
    chunks.extend(emitters.export_emitter_early);
    chunks.extend(emitters.require_emitter);
    chunks.extend(emitters.import_emitter);
    chunks.extend(emitters.export_emitter);
    chunks.join(separator)
}
