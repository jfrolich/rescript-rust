//! CMI file format reader.
//!
//! Parses OCaml compiled module interface (.cmi) files.
//!
//! # File Format
//!
//! A CMI file consists of:
//! 1. Magic number: "Caml1999I024" (12 bytes)
//! 2. Marshal'd value: (cmi_name: string, cmi_sign: Types.signature_item list)
//! 3. Marshal'd value: crcs: (string * Digest.t option) list
//! 4. Marshal'd value: flags: pers_flags list

use std::io::{self, Cursor};

use super::marshal_reader::{MarshalError, MarshalReader, OcamlValue};

/// CMI magic number
const CMI_MAGIC: &[u8; 12] = b"Caml1999I024";

/// CMI file contents (generic, before type interpretation).
#[derive(Debug)]
pub struct CmiInfos {
    /// Module name
    pub cmi_name: String,
    /// Raw signature (generic OCaml values, to be interpreted by sig_reader)
    pub cmi_sign: Vec<OcamlValue>,
    /// CRC checksums: (module_name, optional_digest)
    pub cmi_crcs: Vec<(String, Option<Vec<u8>>)>,
    /// Flags (e.g., deprecation messages)
    pub cmi_flags: Vec<PersFlags>,
}

/// Persistence flags.
#[derive(Debug)]
pub enum PersFlags {
    /// Module is deprecated with the given message.
    Deprecated(String),
}

/// Errors from reading CMI files.
#[derive(Debug)]
pub enum CmiError {
    /// Not a CMI file (bad magic)
    NotAnInterface(String),
    /// Wrong version
    WrongVersion(String, String),
    /// Corrupted file
    Corrupted(String),
    /// Marshal error
    Marshal(MarshalError),
    /// IO error
    Io(io::Error),
}

impl From<MarshalError> for CmiError {
    fn from(e: MarshalError) -> Self {
        CmiError::Marshal(e)
    }
}

impl From<io::Error> for CmiError {
    fn from(e: io::Error) -> Self {
        CmiError::Io(e)
    }
}

impl std::fmt::Display for CmiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CmiError::NotAnInterface(path) => {
                write!(f, "{path}\nis not a compiled interface")
            }
            CmiError::WrongVersion(path, older_newer) => write!(
                f,
                "{path}\nis not a compiled interface for this version of OCaml.\nIt seems to be for {older_newer} version of OCaml."
            ),
            CmiError::Corrupted(path) => write!(f, "Corrupted compiled interface\n{path}"),
            CmiError::Marshal(e) => write!(f, "marshal error: {}", e),
            CmiError::Io(e) => write!(f, "IO error: {}", e),
        }
    }
}

impl std::error::Error for CmiError {}

/// Read a CMI file from a file path.
pub fn read_cmi(filename: &str) -> Result<CmiInfos, CmiError> {
    let data = std::fs::read(filename).map_err(CmiError::Io)?;
    read_cmi_from_bytes(&data, filename)
}

/// Read a CMI file from bytes.
pub fn read_cmi_from_bytes(data: &[u8], filename: &str) -> Result<CmiInfos, CmiError> {
    if data.len() < 12 {
        return Err(CmiError::Corrupted(filename.to_string()));
    }

    // Check magic number
    let magic = &data[..12];
    if magic != CMI_MAGIC {
        // Check if it's a different version
        if magic.starts_with(b"Caml1999I") {
            let older_newer = if magic < CMI_MAGIC {
                "an older"
            } else {
                "a newer"
            };
            return Err(CmiError::WrongVersion(
                filename.to_string(),
                older_newer.to_string(),
            ));
        }
        return Err(CmiError::NotAnInterface(filename.to_string()));
    }

    let mut cursor = Cursor::new(&data[12..]);

    // Read first marshal'd value: (cmi_name, cmi_sign)
    let mut reader = MarshalReader::new();
    let name_and_sign = reader
        .read_with_header(&mut cursor)
        .map_err(|_| CmiError::Corrupted(filename.to_string()))?;

    // The first value is a tuple: (string, signature_item list)
    let (tag, fields) = name_and_sign.as_block();
    if tag != 0 || fields.len() != 2 {
        return Err(CmiError::Corrupted(filename.to_string()));
    }

    let cmi_name = fields[0].as_string().to_string();
    let cmi_sign = fields[1].as_list().into_iter().cloned().collect();

    // Read second marshal'd value: crcs
    let mut reader2 = MarshalReader::new();
    let crcs_value = reader2
        .read_with_header(&mut cursor)
        .map_err(|_| CmiError::Corrupted(filename.to_string()))?;
    let cmi_crcs = read_crcs(&crcs_value);

    // Read third marshal'd value: flags
    let mut reader3 = MarshalReader::new();
    let flags_value = reader3
        .read_with_header(&mut cursor)
        .map_err(|_| CmiError::Corrupted(filename.to_string()))?;
    let cmi_flags = read_flags(&flags_value);

    Ok(CmiInfos {
        cmi_name,
        cmi_sign,
        cmi_crcs,
        cmi_flags,
    })
}

/// Parse CRC list from generic OCaml value.
fn read_crcs(value: &OcamlValue) -> Vec<(String, Option<Vec<u8>>)> {
    let items = value.as_list();
    items
        .into_iter()
        .map(|item| {
            let (tag, fields) = item.as_block();
            assert_eq!(tag, 0); // tuple
            assert_eq!(fields.len(), 2);
            let name = fields[0].as_string().to_string();
            let digest = fields[1].as_option().map(|d| {
                // Digest is a 16-byte string (MD5)
                d.as_string().as_bytes().to_vec()
            });
            (name, digest)
        })
        .collect()
}

/// Parse flags from generic OCaml value.
fn read_flags(value: &OcamlValue) -> Vec<PersFlags> {
    let items = value.as_list();
    items
        .into_iter()
        .map(|item| {
            // pers_flags = Deprecated of string (tag 0, 1 field)
            let (tag, fields) = item.as_block();
            match tag {
                0 => PersFlags::Deprecated(fields[0].as_string().to_string()),
                _ => PersFlags::Deprecated(format!("unknown flag tag {}", tag)),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_magic_check() {
        let data = b"Caml1999I024"; // too short, no marshal data
        let result = read_cmi_from_bytes(data, "test.cmi");
        // Should fail due to missing marshal data, but magic is valid
        assert!(result.is_err());
    }

    #[test]
    fn test_bad_magic() {
        let data = b"NotAValidFile";
        let result = read_cmi_from_bytes(data, "test.cmi");
        assert!(matches!(result, Err(CmiError::NotAnInterface(_))));
    }
}
