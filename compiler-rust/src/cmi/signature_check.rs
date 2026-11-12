//! Opt-in publication oracle infrastructure. No reader consumes its results.
//! Missing comparison implementations are pending, never equality or fallback.
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

    /// Called only after publication. Later slices supply independent shared
    /// graph computations here; do not substitute a portable self-comparison.
    #[cold]
    pub fn after_publication(&self, unit: &str) -> anyhow::Result<()> {
        self.report(unit, [Outcome::Pending, Outcome::Pending, Outcome::Pending])
    }

    fn report(&self, unit: &str, outcomes: [Outcome; 3]) -> anyhow::Result<()> {
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
        };
        let data = serde_json::to_vec(&report)?;
        // Include the outcome in the key. A later successful attempt must not
        // overwrite a mismatch, including when workers compile the same unit.
        let mut key = std::collections::hash_map::DefaultHasher::new();
        data.hash(&mut key);
        std::fs::create_dir_all(directory)?;
        let path = directory.join(format!("{:016x}.json", key.finish()));
        match std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
        {
            Ok(mut file) => file.write_all(&data)?,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.into()),
        }
        for (kind, outcome) in ["fingerprint", "item hashes", "bytes"]
            .into_iter()
            .zip(outcomes)
        {
            if let Outcome::Different { detail } = outcome {
                anyhow::bail!("{unit}: signature equality: {kind}: {detail}");
            }
        }
        Ok(())
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
    /// A graph cannot be compared, for a recorded structural reason.
    NotApplicable {
        /// Why this comparison cannot apply to the unit.
        reason: String,
    },
    /// The independent computation has not been implemented.
    Pending,
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
                [Outcome::fingerprint(1, 2), Outcome::Equal, Outcome::Equal],
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("Unit.res: signature equality: fingerprint")
        );
        check
            .report("Unit.res", [Outcome::Equal, Outcome::Equal, Outcome::Equal])
            .unwrap();
        check
            .report("Unit.res", [Outcome::Equal, Outcome::Equal, Outcome::Equal])
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
            assert_eq!(report["fingerprint"]["status"], "pending");
            std::fs::remove_file(path).unwrap();
        }
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn enabled_mode_requires_a_report_destination() {
        let check = SignatureCheck { directory: None };
        assert!(
            check
                .after_publication("Unit.res")
                .unwrap_err()
                .to_string()
                .contains("RESCRIPT_SIGNATURE_CHECK_REPORTS")
        );
    }
}
