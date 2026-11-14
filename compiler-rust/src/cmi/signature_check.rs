//! The signature equality check (`RESCRIPT_SIGNATURE_CHECK=1`): for every
//! published unit, what the frozen shared graph says of the signature
//! against what its portable form says (`docs/CHECKER_REDESIGN.md`, H.1.7
//! invariant 5). `portable_types::publish_pers_struct_checked` computes the
//! comparison; this module reports it. No reader consumes the results.
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::path::PathBuf;

/// Report destination captured with the opt-in compiler option.
#[derive(Clone, Debug)]
pub struct SignatureCheck {
    directory: Option<PathBuf>,
}

impl SignatureCheck {
    /// Read both variables once, when compiler options are created.
    pub fn from_env() -> Option<Self> {
        (std::env::var("RESCRIPT_SIGNATURE_CHECK").as_deref() == Ok("1")).then(|| Self {
            directory: std::env::var_os("RESCRIPT_SIGNATURE_CHECK_REPORTS").map(PathBuf::from),
        })
    }

    /// Write the report of one publication of `unit`; an error when a
    /// comparison differs or no report directory is configured.
    #[cold]
    pub fn report(&self, unit: &str, comparison: &Comparison) -> anyhow::Result<()> {
        self.prepare(unit, comparison)?.publish()
    }

    /// O(report bytes), only in signature-check mode; no filesystem writes.
    pub(crate) fn prepare(&self, unit: &str, comparison: &Comparison) -> anyhow::Result<PreparedReport> {
        let outcomes = &comparison.outcomes;
        let directory = self.directory.as_ref().ok_or_else(|| {
            anyhow::anyhow!(
                "{unit}: RESCRIPT_SIGNATURE_CHECK_REPORTS is required in signature check mode"
            )
        })?;
        let report = Report {
            unit,
            stage: "signature-equality",
            fingerprint: &outcomes[0],
            item_hashes: &outcomes[1],
            bytes: &outcomes[2],
            shared_graph: comparison.shared_graph,
            carried: &comparison.carried,
        };
        let data = serde_json::to_vec(&report)?;
        // Include the outcome in the key. A later successful attempt must not
        // overwrite a mismatch, including when workers compile the same unit.
        let mut key = std::collections::hash_map::DefaultHasher::new();
        data.hash(&mut key);
        let path = directory.join(format!("{:016x}.json", key.finish()));
        let mut failure = None;
        for (kind, outcome) in ["fingerprint", "item hashes", "bytes"]
            .into_iter()
            .zip(outcomes)
        {
            if let Outcome::Different { detail } = outcome {
                failure = Some(format!(
                    "{unit}: signature equality: {kind}: {detail} (shared graph {})",
                    comparison.shared_graph
                ));
                break;
            }
        }
        Ok(PreparedReport { path, data, failure })
    }

    #[cfg(test)]
    pub(crate) fn for_test(directory: PathBuf) -> Self {
        Self { directory: Some(directory) }
    }
}

/// Private report bytes; dropping these writes nothing.
pub(crate) struct PreparedReport {
    path: PathBuf,
    data: Vec<u8>,
    failure: Option<String>,
}

impl PreparedReport {
    /// O(error text), only on mismatch; no filesystem effects.
    pub(crate) fn validate(&self) -> anyhow::Result<()> {
        match &self.failure {
            Some(error) => anyhow::bail!("{error}"),
            None => Ok(()),
        }
    }

    /// O(report bytes), once the owning attempt commits.
    pub(crate) fn publish(self) -> anyhow::Result<()> {
        std::fs::create_dir_all(self.path.parent().expect("report directory"))?;
        match std::fs::OpenOptions::new().write(true).create_new(true).open(&self.path) {
            Ok(mut file) => file.write_all(&self.data)?,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.into()),
        }
        self.validate()
    }
}

/// The comparison of one publication.
#[derive(Debug, Clone)]
pub struct Comparison {
    /// Fingerprint, item digests and encoded bytes, in this order.
    pub outcomes: [Outcome; 3],
    /// Where the shared graph came from: `published` (the graph dependents
    /// read), or `forced: <why>` when check mode built one that a normal
    /// build would not have at publication.
    pub shared_graph: &'static str,
    /// Which data the frozen graph does not hold and the byte comparison
    /// had to be given (`shared_reader::Carried`), by name.
    pub carried: Vec<&'static str>,
}

impl Comparison {
    /// No shared graph could be built for the unit.
    pub fn not_applicable(shared_graph: &'static str, reason: &str) -> Self {
        let outcome = || Outcome::NotApplicable {
            reason: reason.to_string(),
        };
        Comparison {
            outcomes: [outcome(), outcome(), outcome()],
            shared_graph,
            carried: Vec::new(),
        }
    }

    #[cfg(test)]
    fn of(outcomes: [Outcome; 3]) -> Self {
        Comparison {
            outcomes,
            shared_graph: "published",
            carried: Vec::new(),
        }
    }
}

/// Result of one independent signature comparison.
#[derive(Debug, Clone, serde::Serialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum Outcome {
    /// Both independently computed values match.
    Equal,
    /// A mismatch that must fail compilation.
    Different {
        /// First differing value or byte offset.
        detail: String,
    },
    /// No shared graph exists to compare with, for a recorded reason.
    NotApplicable {
        /// Why this comparison cannot apply to the unit.
        reason: String,
    },
}

impl Outcome {
    /// Compare the existing and independently computed structural fingerprint.
    pub fn fingerprint(portable: u64, shared: u64) -> Self {
        if portable == shared {
            Self::Equal
        } else {
            Self::Different {
                detail: format!("{portable:016x} != {shared:016x}"),
            }
        }
    }

    /// Linear in the encoded length, including unequal-length prefix cases.
    pub fn bytes(portable: &[u8], shared: &[u8]) -> Self {
        match portable.iter().zip(shared).position(|(a, b)| a != b) {
            Some(offset) => Self::Different {
                detail: format!("first differing byte offset {offset}"),
            },
            None if portable.len() != shared.len() => Self::Different {
                detail: format!(
                    "first differing byte offset {} (length {} != {})",
                    portable.len().min(shared.len()),
                    portable.len(),
                    shared.len()
                ),
            },
            None => Self::Equal,
        }
    }

    /// Compare in declaration order: shadowed item names are not deduplicated.
    /// Linear in the number of entries, with constant-sized kind/name keys.
    pub fn item_hashes<K: PartialEq + std::fmt::Debug>(
        portable: &[(K, u64)],
        shared: &[(K, u64)],
    ) -> Self {
        for (index, (a, b)) in portable.iter().zip(shared).enumerate() {
            if a != b {
                return Self::Different {
                    detail: format!("item {index}: {a:?} != {b:?}"),
                };
            }
        }
        if portable.len() != shared.len() {
            Self::Different {
                detail: format!(
                    "item {} missing (length {} != {})",
                    portable.len().min(shared.len()),
                    portable.len(),
                    shared.len()
                ),
            }
        } else {
            Self::Equal
        }
    }
}

#[derive(serde::Serialize)]
struct Report<'a> {
    unit: &'a str,
    stage: &'static str,
    fingerprint: &'a Outcome,
    item_hashes: &'a Outcome,
    bytes: &'a Outcome,
    shared_graph: &'a str,
    carried: &'a [&'static str],
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comparisons_name_the_first_difference() {
        assert!(matches!(Outcome::fingerprint(7, 7), Outcome::Equal));
        assert!(matches!(
            Outcome::fingerprint(7, 8),
            Outcome::Different { .. }
        ));
        assert!(matches!(Outcome::bytes(b"abc", b"abc"), Outcome::Equal));
        for bytes in [b"abd".as_slice(), b"ab".as_slice()] {
            let Outcome::Different { detail } = Outcome::bytes(b"abc", bytes) else {
                panic!()
            };
            assert!(detail.contains("offset 2"));
        }
        let items = [("x", 1), ("x", 2)];
        assert!(matches!(
            Outcome::item_hashes(&items, &items),
            Outcome::Equal
        ));
        let Outcome::Different { detail } = Outcome::item_hashes(&items, &[("x", 1), ("x", 3)])
        else {
            panic!()
        };
        assert!(detail.contains("item 1"));
        assert!(matches!(
            Outcome::item_hashes(&items, &items[..1]),
            Outcome::Different { .. }
        ));
    }

    #[test]
    fn immutable_reports_preserve_failure_and_error_names_unit() {
        let directory =
            std::env::temp_dir().join(format!("signature-check-{}", std::process::id()));
        let check = SignatureCheck {
            directory: Some(directory.clone()),
        };
        let error = check
            .report(
                "Unit.res",
                &Comparison::of([Outcome::fingerprint(1, 2), Outcome::Equal, Outcome::Equal]),
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("Unit.res: signature equality: fingerprint")
        );
        check
            .report(
                "Unit.res",
                &Comparison::of([Outcome::Equal, Outcome::Equal, Outcome::Equal]),
            )
            .unwrap();
        check
            .report(
                "Unit.res",
                &Comparison::of([Outcome::Equal, Outcome::Equal, Outcome::Equal]),
            )
            .unwrap();
        let files: Vec<_> = std::fs::read_dir(&directory).unwrap().collect();
        assert_eq!(files.len(), 2);
        for file in files {
            std::fs::remove_file(file.unwrap().path()).unwrap();
        }
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn both_publication_paths_report_without_changing_output() {
        let directory = std::env::temp_dir().join(format!(
            "signature-publication-check-{}",
            std::process::id()
        ));
        let mut options = crate::driver::CompilerOptions {
            nopervasives: true,
            signature_check: None,
            ..Default::default()
        };
        let compile = |options: &crate::driver::CompilerOptions| {
            crate::driver::compile_source_in_process(
                "let answer = 42",
                "Oracle.res",
                "Oracle",
                options,
                &crate::cmi::persistent_env::ModuleRegistry::new(),
                false,
                None,
            )
            .unwrap()
            .js_output
        };
        let expected = compile(&options);
        options.signature_check = Some(SignatureCheck {
            directory: Some(directory.clone()),
        });
        assert_eq!(compile(&options), expected);
        crate::driver::typecheck_interface_source_in_process(
            "let answer: int",
            "Oracle.resi",
            "Oracle",
            &options,
            &crate::cmi::persistent_env::ModuleRegistry::new(),
        )
        .unwrap();
        let files: Vec<_> = std::fs::read_dir(&directory).unwrap().collect();
        assert_eq!(files.len(), 2);
        for file in files {
            let path = file.unwrap().path();
            let report: serde_json::Value =
                serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
            for kind in ["fingerprint", "item_hashes", "bytes"] {
                assert_eq!(report[kind]["status"], "equal", "{report}");
            }
            assert_eq!(report["shared_graph"], "published");
            std::fs::remove_file(path).unwrap();
        }
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn every_kind_of_type_node_reads_back_equal_from_the_shared_graph() {
        let directory =
            std::env::temp_dir().join(format!("signature-kinds-check-{}", std::process::id()));
        let options = crate::driver::CompilerOptions {
            nopervasives: true,
            signature_check: Some(SignatureCheck {
                directory: Some(directory.clone()),
            }),
            ..Default::default()
        };
        // Variables shared between positions, rows, objects, a package
        // type, labelled and optional parameters, a recursive type, inline
        // and optional record fields, an unboxed variant, extensions and a
        // nested signature.
        crate::driver::typecheck_interface_source_in_process(
            r#"
type color = [#red | #green(int)]
type openColor<'a> = [> #red | #blue(string)] as 'a
type obj = {"x": int, "y": string}
type rec tree<'a> = Leaf | Node(tree<'a>, 'a, tree<'a>)
@unboxed type u = I(int) | S(string)
type r = {mutable a: int, b?: string}
type t = A({x: int}) | B
module type S = {
  type t
  let x: t
}
let pack: module(S with type t = int)
let f: (~a: int, ~b: string=?, 'c) => ('c, 'c)
let g: 'a => 'a
module M: {
  type t
  let make: unit => t
  let pair: t => (t, t)
}
exception E(int)
type ext = ..
type ext += X(int)
"#,
            "Kinds.resi",
            "Kinds",
            &options,
            &crate::cmi::persistent_env::ModuleRegistry::new(),
        )
        .unwrap();
        let files: Vec<_> = std::fs::read_dir(&directory).unwrap().collect();
        assert_eq!(files.len(), 1);
        for file in files {
            let path = file.unwrap().path();
            let report: serde_json::Value =
                serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
            for kind in ["fingerprint", "item_hashes", "bytes"] {
                assert_eq!(report[kind]["status"], "equal", "{report}");
            }
            std::fs::remove_file(path).unwrap();
        }
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn enabled_mode_requires_a_report_destination() {
        let check = SignatureCheck { directory: None };
        assert!(
            check
                .report(
                    "Unit.res",
                    &Comparison::of([Outcome::Equal, Outcome::Equal, Outcome::Equal])
                )
                .unwrap_err()
                .to_string()
                .contains("RESCRIPT_SIGNATURE_CHECK_REPORTS")
        );
    }
}
