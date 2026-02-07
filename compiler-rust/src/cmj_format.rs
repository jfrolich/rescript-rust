//! CMJ (compiled JS metadata) format handling.
//!
//! This mirrors js_cmj_format.ml: a digest header followed by a Marshal payload.

use std::fs;
use std::path::Path;

use crate::binary_ast::marshal::{MarshalReader, MarshalValue, MarshalValueRef, MarshalWriter};

/// Raw CMJ payload with digest.
#[derive(Debug, Clone)]
pub struct CmjRaw {
    pub digest: [u8; 16],
    pub payload: MarshalValueRef,
}

/// CMJ table (placeholder).
#[derive(Debug, Clone)]
pub struct CmjTable {
    pub raw: Option<CmjRaw>,
}

impl CmjTable {
    pub fn empty() -> Self {
        CmjTable { raw: None }
    }
}

/// Read a .cmj file from disk.
pub fn read_cmj(path: &Path) -> Result<CmjTable, String> {
    let bytes = fs::read(path).map_err(|err| err.to_string())?;
    if bytes.len() < 16 {
        return Err("CMJ file too short".to_string());
    }
    let mut digest = [0u8; 16];
    digest.copy_from_slice(&bytes[..16]);
    let (payload, _next_offset) = read_marshaled_value(&bytes[16..])?;
    Ok(CmjTable {
        raw: Some(CmjRaw { digest, payload }),
    })
}

/// Write a .cmj file to disk.
pub fn write_cmj(path: &Path, table: &CmjTable) -> Result<(), String> {
    let payload = if let Some(raw) = &table.raw {
        raw.payload.clone()
    } else {
        build_empty_payload()
    };

    let payload_bytes = marshal_value_bytes(&payload);
    let digest = md5::compute(&payload_bytes);

    let mut bytes = Vec::new();
    bytes.extend_from_slice(&digest.0);
    bytes.extend_from_slice(&payload_bytes);

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

fn build_empty_payload() -> MarshalValueRef {
    let empty_values = MarshalValue::shared(MarshalValue::Int(0));
    let pure = MarshalValue::shared(MarshalValue::Int(1));
    let package_spec = MarshalValue::shared(MarshalValue::Int(0));
    let case = MarshalValue::shared(MarshalValue::Int(0));
    MarshalValue::shared(MarshalValue::Block {
        tag: 0,
        fields: vec![empty_values, pure, package_spec, case],
    })
}
