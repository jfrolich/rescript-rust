//! CMI file format reader.
//!
//! Parses OCaml compiled module interface (.cmi) files.
//!
//! # File Format
//!
//! A CMI file consists of:
//! 1. Magic number: "Caml1999I036" (12 bytes)
//! 2. Marshal'd value: (cmi_name: string, cmi_sign: Types.signature_item list)
//! 3. Marshal'd value: crcs: (string * Digest.t option) list
//! 4. Marshal'd value: flags: pers_flags list

use std::io::{self, Cursor};

use super::marshal_reader::{MarshalError, MarshalReader, OcamlValue};

/// CMI magic number
const CMI_MAGIC: &[u8; 12] = b"Caml1999I036";

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

    let corrupted = || CmiError::Corrupted(filename.to_string());

    // The first value is a tuple: (string, signature_item list)
    let (cmi_name, cmi_sign) = match name_and_sign.as_block_opt() {
        Some((0, [name, sign])) => (
            name.as_string_opt().ok_or_else(corrupted)?.to_string(),
            sign.try_list()
                .ok_or_else(corrupted)?
                .into_iter()
                .cloned()
                .collect(),
        ),
        _ => return Err(corrupted()),
    };

    // Read second marshal'd value: crcs
    let mut reader2 = MarshalReader::new();
    let crcs_value = reader2
        .read_with_header(&mut cursor)
        .map_err(|_| CmiError::Corrupted(filename.to_string()))?;
    let cmi_crcs = read_crcs(&crcs_value).ok_or_else(corrupted)?;

    // Read third marshal'd value: flags
    let mut reader3 = MarshalReader::new();
    let flags_value = reader3
        .read_with_header(&mut cursor)
        .map_err(|_| CmiError::Corrupted(filename.to_string()))?;
    let cmi_flags = read_flags(&flags_value).ok_or_else(corrupted)?;

    Ok(CmiInfos {
        cmi_name,
        cmi_sign,
        cmi_crcs,
        cmi_flags,
    })
}

/// The CRC list of a `.cmi` file (`cmi_crcs`, the second marshalled value,
/// cmi_format.ml:67-76), without decoding its signature.
pub fn read_cmi_crcs(filename: &str) -> Option<Vec<(String, Option<[u8; 16]>)>> {
    let data = std::fs::read(filename).ok()?;
    if data.len() < 12 || &data[..12] != CMI_MAGIC {
        return None;
    }
    // Skip the (name, signature) value: a 20-byte marshal header whose
    // second word is the data length (intern.c `caml_input_val_from_bytes`).
    let header = data.get(12..32)?;
    if header[..4] != [0x84, 0x95, 0xA6, 0xBE] {
        return None;
    }
    let data_len = u32::from_be_bytes([header[4], header[5], header[6], header[7]]) as usize;
    let crcs_start = 32usize.checked_add(data_len)?;
    let mut cursor = Cursor::new(data.get(crcs_start..)?);
    let mut reader = MarshalReader::new();
    let crcs_value = reader.read_with_header(&mut cursor).ok()?;
    Some(
        read_crcs(&crcs_value)?
            .into_iter()
            .map(|(name, crc)| (name, crc.and_then(|crc| <[u8; 16]>::try_from(crc).ok())))
            .collect(),
    )
}

/// Parse CRC list from generic OCaml value, `None` when malformed.
fn read_crcs(value: &OcamlValue) -> Option<Vec<(String, Option<Vec<u8>>)>> {
    value
        .try_list()?
        .into_iter()
        .map(|item| {
            // (string * Digest.t option) tuple
            let Some((0, [name, digest])) = item.as_block_opt() else {
                return None;
            };
            let name = name.as_string_opt()?.to_string();
            let digest = match digest {
                OcamlValue::Int(0) => None,
                // Digest is a 16-byte string (MD5); marshalled strings are
                // decoded one char per byte.
                OcamlValue::Block(0, fields) if fields.len() == 1 => Some(
                    fields[0]
                        .as_string_opt()?
                        .chars()
                        .map(|c| c as u8)
                        .collect::<Vec<u8>>(),
                ),
                _ => return None,
            };
            Some((name, digest))
        })
        .collect()
}

/// Parse flags from generic OCaml value, `None` when malformed.
fn read_flags(value: &OcamlValue) -> Option<Vec<PersFlags>> {
    value
        .try_list()?
        .into_iter()
        .map(|item| match item.as_block_opt() {
            // pers_flags = Deprecated of string (tag 0, 1 field)
            Some((0, [message])) => {
                Some(PersFlags::Deprecated(message.as_string_opt()?.to_string()))
            }
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_magic_check() {
        let data = b"Caml1999I036"; // too short, no marshal data
        let result = read_cmi_from_bytes(data, "test.cmi");
        // Should fail due to missing marshal data, but magic is valid
        assert!(result.is_err());
    }

    #[test]
    fn malformed_crcs_and_flags_are_rejected() {
        let s = |v: &str| OcamlValue::String(v.to_string());
        let block = |tag, fields: Vec<OcamlValue>| OcamlValue::Block(tag, fields.into());
        let cons = |head, tail| block(0, vec![head, tail]);
        let nil = OcamlValue::Int(0);

        let crc = cons(block(0, vec![s("M"), nil.clone()]), nil.clone());
        let crcs = read_crcs(&crc).unwrap();
        assert_eq!(crcs.len(), 1);
        assert_eq!(crcs[0].0, "M");
        assert!(crcs[0].1.is_none());
        assert!(read_crcs(&cons(OcamlValue::Int(3), nil.clone())).is_none());
        assert!(read_crcs(&s("not a list")).is_none());

        let flag = cons(block(0, vec![s("old")]), nil.clone());
        assert!(matches!(
            read_flags(&flag).unwrap().as_slice(),
            [PersFlags::Deprecated(message)] if message == "old"
        ));
        assert!(read_flags(&cons(block(1, vec![s("x")]), nil)).is_none());
    }

    #[test]
    fn test_bad_magic() {
        let data = b"NotAValidFile";
        let result = read_cmi_from_bytes(data, "test.cmi");
        assert!(matches!(result, Err(CmiError::NotAnInterface(_))));
    }
}
