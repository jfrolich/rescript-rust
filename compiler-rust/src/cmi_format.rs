//! CMI (compiled interface) format handling.
//!
//! This module mirrors OCaml's cmi_format implementation, using OCaml Marshal
//! encoding for data and the standard CMI magic number.

use std::fs;
use std::path::Path;

use crate::binary_ast::marshal::{MarshalReader, MarshalValue, MarshalValueRef, MarshalWriter};
use crate::types::Signature;

/// Magic number for OCaml .cmi files.
pub const CMI_MAGIC_NUMBER: &str = "Caml1999I022";

/// CMI persistent flags.
#[derive(Debug, Clone)]
pub enum PersFlag {
    /// Deprecated interface with message.
    Deprecated(String),
}

/// Raw marshaled CMI values.
#[derive(Debug, Clone)]
pub struct CmiRaw {
    pub payload: MarshalValueRef,
    pub crcs: MarshalValueRef,
    pub flags: MarshalValueRef,
}

/// CMI information.
#[derive(Debug, Clone)]
pub struct CmiInfos {
    pub cmi_name: String,
    pub cmi_sign: Signature,
    pub cmi_crcs: Vec<(String, Option<Vec<u8>>)>,
    pub cmi_flags: Vec<PersFlag>,
    pub raw: Option<CmiRaw>,
}

impl CmiInfos {
    pub fn empty(name: String) -> Self {
        CmiInfos {
            cmi_name: name,
            cmi_sign: Vec::new(),
            cmi_crcs: Vec::new(),
            cmi_flags: Vec::new(),
            raw: None,
        }
    }
}

/// Read a .cmi file from disk.
pub fn read_cmi(path: &Path) -> Result<CmiInfos, String> {
    let bytes = fs::read(path).map_err(|err| err.to_string())?;
    if bytes.len() < CMI_MAGIC_NUMBER.len() {
        return Err("CMI file too short".to_string());
    }
    let magic = &bytes[..CMI_MAGIC_NUMBER.len()];
    if magic != CMI_MAGIC_NUMBER.as_bytes() {
        return Err("Invalid CMI magic number".to_string());
    }

    let mut offset = CMI_MAGIC_NUMBER.len();
    let (payload, next_offset) = read_marshaled_value(&bytes[offset..])?;
    offset += next_offset;
    let (crcs, next_offset) = read_marshaled_value(&bytes[offset..])?;
    offset += next_offset;
    let (flags, _final_offset) = read_marshaled_value(&bytes[offset..])?;

    let name = extract_cmi_name(&payload).unwrap_or_else(|| "".to_string());

    Ok(CmiInfos {
        cmi_name: name,
        cmi_sign: Vec::new(),
        cmi_crcs: Vec::new(),
        cmi_flags: Vec::new(),
        raw: Some(CmiRaw {
            payload,
            crcs,
            flags,
        }),
    })
}

/// Write a .cmi file to disk.
pub fn write_cmi(path: &Path, cmi: &CmiInfos) -> Result<(), String> {
    let (payload, crcs, flags) = if let Some(raw) = &cmi.raw {
        (raw.payload.clone(), raw.crcs.clone(), raw.flags.clone())
    } else {
        let payload = build_payload(cmi);
        let crcs = build_crcs(cmi, &payload);
        let flags = build_flags(cmi);
        (payload, crcs, flags)
    };

    let mut bytes = Vec::new();
    bytes.extend_from_slice(CMI_MAGIC_NUMBER.as_bytes());
    bytes.extend_from_slice(&marshal_value_bytes(&payload));
    bytes.extend_from_slice(&marshal_value_bytes(&crcs));
    bytes.extend_from_slice(&marshal_value_bytes(&flags));

    fs::write(path, bytes).map_err(|err| err.to_string())
}

fn marshal_value_bytes(value: &MarshalValueRef) -> Vec<u8> {
    let mut writer = MarshalWriter::new();
    MarshalValue::marshal_value(value, &mut writer);
    writer.finish()
}

fn read_marshaled_value(bytes: &[u8]) -> Result<(MarshalValueRef, usize), String> {
    let mut reader = MarshalReader::new(bytes)?;
    let value = reader.read_value()?;
    let end = reader.end_offset();
    Ok((value, end))
}

fn build_payload(cmi: &CmiInfos) -> MarshalValueRef {
    let name = MarshalValue::shared(MarshalValue::Bytes(cmi.cmi_name.as_bytes().to_vec()));
    let empty_sign = MarshalValue::shared(MarshalValue::Int(0));
    let payload = MarshalValue::Block {
        tag: 0,
        fields: vec![name, empty_sign],
    };
    MarshalValue::shared(payload)
}

fn build_crcs(cmi: &CmiInfos, payload: &MarshalValueRef) -> MarshalValueRef {
    let payload_bytes = marshal_value_bytes(payload);
    let mut content = Vec::new();
    content.extend_from_slice(CMI_MAGIC_NUMBER.as_bytes());
    content.extend_from_slice(&payload_bytes);
    let digest = md5::compute(&content);

    let name = MarshalValue::shared(MarshalValue::Bytes(cmi.cmi_name.as_bytes().to_vec()));
    let digest_value = MarshalValue::shared(MarshalValue::Bytes(digest.0.to_vec()));
    let digest_opt = MarshalValue::shared(MarshalValue::Block {
        tag: 0,
        fields: vec![digest_value],
    });
    let pair = MarshalValue::shared(MarshalValue::Block {
        tag: 0,
        fields: vec![name, digest_opt],
    });

    list_from_vec(vec![pair])
}

fn build_flags(cmi: &CmiInfos) -> MarshalValueRef {
    if cmi.cmi_flags.is_empty() {
        return MarshalValue::shared(MarshalValue::Int(0));
    }
    let mut flags = Vec::new();
    for flag in &cmi.cmi_flags {
        let value = match flag {
            PersFlag::Deprecated(msg) => MarshalValue::Block {
                tag: 0,
                fields: vec![MarshalValue::shared(MarshalValue::Bytes(
                    msg.as_bytes().to_vec(),
                ))],
            },
        };
        flags.push(MarshalValue::shared(value));
    }
    list_from_vec(flags)
}

fn list_from_vec(items: Vec<MarshalValueRef>) -> MarshalValueRef {
    if items.is_empty() {
        return MarshalValue::shared(MarshalValue::Int(0));
    }
    let mut tail = MarshalValue::shared(MarshalValue::Int(0));
    for item in items.into_iter().rev() {
        tail = MarshalValue::shared(MarshalValue::Block {
            tag: 0,
            fields: vec![item, tail],
        });
    }
    tail
}

fn extract_cmi_name(payload: &MarshalValueRef) -> Option<String> {
    let payload = payload.borrow();
    match &*payload {
        MarshalValue::Block { tag: 0, fields } if fields.len() == 2 => {
            if let MarshalValue::Bytes(bytes) = &*fields[0].borrow() {
                return Some(String::from_utf8_lossy(bytes).to_string());
            }
            None
        }
        _ => None,
    }
}
