//! OCaml Marshal binary format reader.
//!
//! Reads OCaml's `Marshal.to_string` output format into a generic value tree.
//! The format is documented in OCaml's `runtime/caml/intext.h` and `runtime/extern.c`.
//!
//! # Format Overview
//!
//! - 4-byte magic number: 0x8495A6BE (small format)
//! - 16-byte header: data_len (4), obj_count (4), size_32 (4), size_64 (4)
//! - Payload: encoded values using prefix and explicit opcodes
//!
//! # Value Encoding
//!
//! - Integers: PREFIX_SMALL_INT (0-63), CODE_INT8, CODE_INT16, CODE_INT32, CODE_INT64
//! - Strings: PREFIX_SMALL_STRING (0-31 bytes), CODE_STRING8, CODE_STRING32
//! - Blocks: PREFIX_SMALL_BLOCK (tag 0-15, size 0-7), CODE_BLOCK32
//! - Sharing: CODE_SHARED8/16/32 (back-references to already-read objects)

use std::io::{self, Cursor, Read};
use std::sync::Arc;

/// Magic number for small Marshal format
const MAGIC_NUMBER_SMALL: u32 = 0x8495A6BE;

/// Prefix codes
const PREFIX_SMALL_BLOCK: u8 = 0x80;
const PREFIX_SMALL_INT: u8 = 0x40;
const PREFIX_SMALL_STRING: u8 = 0x20;

/// Explicit opcodes
const CODE_INT8: u8 = 0x00;
const CODE_INT16: u8 = 0x01;
const CODE_INT32: u8 = 0x02;
const CODE_INT64: u8 = 0x03;
const CODE_SHARED8: u8 = 0x04;
const CODE_SHARED16: u8 = 0x05;
const CODE_SHARED32: u8 = 0x06;
const CODE_BLOCK32: u8 = 0x08;
const CODE_STRING8: u8 = 0x09;
const CODE_STRING32: u8 = 0x0A;
const CODE_DOUBLE_BIG: u8 = 0x0B;
const CODE_DOUBLE_LITTLE: u8 = 0x0C;
const CODE_CUSTOM_FIXED: u8 = 0x19;
const CUSTOM_INT32_ID: &[u8] = b"_i\0";

/// A generic OCaml value read from the Marshal format.
#[derive(Debug, Clone)]
pub enum OcamlValue {
    /// An integer value (OCaml `int`, also used for bool, constant constructors, unit, etc.)
    Int(i64),
    /// A string value
    String(OcamlString),
    /// A block (record, variant with args, tuple, array, etc.)
    /// Fields: (tag, fields)
    Block(u8, Arc<[OcamlValue]>),
    /// A 64-bit float
    Float(f64),
}

/// Owned string contents with the allocation identity recorded by the decoder.
/// Cloning a marshal back-reference retains its token, not just equal text.
/// Synthetic values have no allocation evidence.
#[derive(Debug, Clone)]
pub struct OcamlString {
    text: String,
    allocation: u64,
}

impl From<String> for OcamlString {
    fn from(text: String) -> Self {
        Self {
            text,
            allocation: 0,
        }
    }
}

impl From<&str> for OcamlString {
    fn from(text: &str) -> Self {
        text.to_string().into()
    }
}

impl std::ops::Deref for OcamlString {
    type Target = str;
    fn deref(&self) -> &str {
        &self.text
    }
}

impl OcamlString {
    /// A string decoded at `allocation` (scope in the high half).
    #[cfg(test)]
    pub(crate) fn decoded(text: &str, allocation: u64) -> Self {
        Self {
            text: text.to_string(),
            allocation,
        }
    }

    /// The string's text.
    pub fn as_str(&self) -> &str {
        &self.text
    }

    pub(crate) fn allocation(&self) -> Option<(u64, u32)> {
        (self.allocation != 0).then_some((
            self.allocation & 0xffff_ffff_0000_0000,
            self.allocation as u32,
        ))
    }
}

impl OcamlValue {
    /// Get as integer, or panic.
    pub fn as_int(&self) -> i64 {
        match self {
            OcamlValue::Int(n) => *n,
            _ => panic!("expected Int, got {:?}", self.short_debug()),
        }
    }

    /// Get as string, or panic.
    pub fn as_string(&self) -> &str {
        match self {
            OcamlValue::String(s) => s,
            _ => panic!("expected String, got {:?}", self.short_debug()),
        }
    }

    /// Get as block, or panic. Returns (tag, fields).
    pub fn as_block(&self) -> (u8, &[OcamlValue]) {
        match self {
            OcamlValue::Block(tag, fields) => (*tag, fields.as_ref()),
            _ => panic!("expected Block, got {:?}", self.short_debug()),
        }
    }

    /// Try to get as block, returning None if not a block.
    pub fn as_block_opt(&self) -> Option<(u8, &[OcamlValue])> {
        match self {
            OcamlValue::Block(tag, fields) => Some((*tag, fields.as_ref())),
            _ => None,
        }
    }

    /// Get as bool (Int 0 = false, Int 1 = true).
    pub fn as_bool(&self) -> bool {
        self.as_int() != 0
    }

    /// Check if this is None (Int 0).
    pub fn is_none(&self) -> bool {
        matches!(self, OcamlValue::Int(0))
    }

    /// Get the Some value from an Option (`Block(0, [value])`), or None if `Int(0)`.
    pub fn as_option(&self) -> Option<&OcamlValue> {
        match self {
            OcamlValue::Int(0) => None,
            OcamlValue::Block(0, fields) if fields.len() == 1 => Some(&fields[0]),
            _ => panic!("expected Option, got {:?}", self.short_debug()),
        }
    }

    /// Iterate over a list value. Returns items in order.
    pub fn as_list(&self) -> Vec<&OcamlValue> {
        let mut result = Vec::new();
        let mut current = self;
        loop {
            match current {
                OcamlValue::Int(0) => break,
                OcamlValue::Block(0, fields) if fields.len() == 2 => {
                    result.push(&fields[0]);
                    current = &fields[1];
                }
                _ => panic!("expected list, got {:?}", current.short_debug()),
            }
        }
        result
    }

    /// Iterate over a list value, or `None` when it is not a well-formed
    /// list.
    pub fn try_list(&self) -> Option<Vec<&OcamlValue>> {
        let mut result = Vec::new();
        let mut current = self;
        loop {
            match current {
                OcamlValue::Int(0) => return Some(result),
                OcamlValue::Block(0, fields) if fields.len() == 2 => {
                    result.push(&fields[0]);
                    current = &fields[1];
                }
                _ => return None,
            }
        }
    }

    /// Get as string, or `None` when it is not a string.
    pub fn as_string_opt(&self) -> Option<&str> {
        match self {
            OcamlValue::String(s) => Some(s),
            _ => None,
        }
    }

    /// Get block field at index.
    pub fn field(&self, idx: usize) -> &OcamlValue {
        match self {
            OcamlValue::Block(_, fields) => &fields[idx],
            _ => panic!(
                "expected Block for field access, got {:?}",
                self.short_debug()
            ),
        }
    }

    /// Get block tag.
    pub fn tag(&self) -> u8 {
        match self {
            OcamlValue::Block(tag, _) => *tag,
            _ => panic!("expected Block for tag, got {:?}", self.short_debug()),
        }
    }

    /// Short debug representation (doesn't recurse deeply).
    pub fn short_debug(&self) -> String {
        match self {
            OcamlValue::Int(n) => format!("Int({})", n),
            OcamlValue::String(s) => {
                if let Some((cut, _)) = s.char_indices().nth(50) {
                    format!("String(\"{}...\")", &s[..cut])
                } else {
                    format!("String(\"{}\")", s.as_str())
                }
            }
            OcamlValue::Block(tag, fields) => {
                format!("Block(tag={}, {} fields)", tag, fields.len())
            }
            OcamlValue::Float(f) => format!("Float({})", f),
        }
    }
}

/// Errors from reading Marshal format.
#[derive(Debug)]
pub enum MarshalError {
    /// Invalid magic number
    BadMagic(u32),
    /// IO error
    Io(io::Error),
    /// Invalid opcode
    BadOpcode(u8),
    /// Invalid shared reference (distance out of range)
    BadSharedRef(u32),
    /// Unexpected end of data
    UnexpectedEof,
}

impl From<io::Error> for MarshalError {
    fn from(e: io::Error) -> Self {
        MarshalError::Io(e)
    }
}

impl std::fmt::Display for MarshalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MarshalError::BadMagic(m) => write!(f, "bad marshal magic: 0x{:08X}", m),
            MarshalError::Io(e) => write!(f, "IO error: {}", e),
            MarshalError::BadOpcode(c) => write!(f, "bad marshal opcode: 0x{:02X}", c),
            MarshalError::BadSharedRef(d) => write!(f, "bad shared ref distance: {}", d),
            MarshalError::UnexpectedEof => write!(f, "unexpected end of marshal data"),
        }
    }
}

impl std::error::Error for MarshalError {}

/// Reader for OCaml Marshal binary format.
#[derive(Default)]
pub struct MarshalReader {
    /// The object table for shared references.
    /// Each object is assigned an index as it's read; shared references
    /// refer back to earlier objects by distance.
    obj_table: Vec<OcamlValue>,
    string_scope: u32,
}

impl MarshalReader {
    /// Create a new reader.
    pub fn new() -> Self {
        Self::default()
    }

    fn decoded_string(&mut self, text: String) -> OcamlValue {
        if self.string_scope == 0 {
            // Reuse the checked owner namespace: no pointer identity or new
            // process-global allocator is needed for decoded string scopes.
            self.string_scope = crate::types::decl_loc::next_table_owner();
        }
        let index = u32::try_from(self.obj_table.len()).expect("marshal object table exhausted");
        OcamlValue::String(OcamlString {
            text,
            allocation: ((self.string_scope as u64) << 32) | index as u64,
        })
    }

    /// Read a marshalled value from bytes (including magic + header).
    pub fn read_from_bytes(&mut self, data: &[u8]) -> Result<OcamlValue, MarshalError> {
        let mut cursor = Cursor::new(data);
        self.read_with_header(&mut cursor)
    }

    /// Read a marshalled value including magic number and header.
    pub fn read_with_header<R: Read>(
        &mut self,
        reader: &mut R,
    ) -> Result<OcamlValue, MarshalError> {
        let magic = read_u32_be(reader)?;
        if magic != MAGIC_NUMBER_SMALL {
            return Err(MarshalError::BadMagic(magic));
        }

        // Header: data_len, obj_count, size_32, size_64.
        let data_len = read_u32_be(reader)?;
        let obj_count = read_u32_be(reader)?;
        let _size_32 = read_u32_be(reader)?;
        let _size_64 = read_u32_be(reader)?;

        self.obj_table.clear();
        self.string_scope = 0;
        // Every object takes at least one byte of payload, so `data_len`
        // bounds a corrupt `obj_count`.
        self.obj_table.reserve(obj_count.min(data_len) as usize);
        self.read_value(reader)
    }

    /// Read a marshalled value without magic/header (raw payload).
    /// Uses an explicit stack instead of recursion to handle deeply nested structures.
    pub fn read_value<R: Read>(&mut self, reader: &mut R) -> Result<OcamlValue, MarshalError> {
        // Stack of pending block constructions.
        // Each entry: (tag, obj_table_index, total_field_count, fields_so_far)
        let mut stack: Vec<(u8, usize, usize, Vec<OcamlValue>)> = Vec::new();

        loop {
            // Read the next atomic value (non-block) or start a new block
            let value = self.read_atom(reader, &mut stack)?;

            // If we got a value back, try to complete pending blocks
            if let Some(mut val) = value {
                loop {
                    match stack.last_mut() {
                        None => {
                            // No pending blocks - this is the root value
                            return Ok(val);
                        }
                        Some((tag, obj_idx, total, fields)) => {
                            fields.push(val);
                            if fields.len() == *total {
                                // Block is complete
                                let completed =
                                    OcamlValue::Block(*tag, Arc::from(std::mem::take(fields)));
                                self.obj_table[*obj_idx] = completed.clone();
                                val = completed;
                                stack.pop();
                                // Continue popping - this completed block might be a field of an outer block
                            } else {
                                // Need more fields - break out to read the next value
                                break;
                            }
                        }
                    }
                }
            }
            // If value was None, a block was pushed onto the stack and we need to read its fields
        }
    }

    /// Read a single atom (non-block value) or push a new block frame onto the stack.
    /// Returns Some(value) for atomic values, None when a block frame was pushed.
    fn read_atom<R: Read>(
        &mut self,
        reader: &mut R,
        stack: &mut Vec<(u8, usize, usize, Vec<OcamlValue>)>,
    ) -> Result<Option<OcamlValue>, MarshalError> {
        let code = read_u8(reader)?;

        // Check prefix codes first (high bits)
        if code >= PREFIX_SMALL_BLOCK {
            let tag = code & 0x0F;
            let size = ((code >> 4) & 0x07) as usize;
            if size == 0 {
                // Empty block - complete immediately
                let value = OcamlValue::Block(tag, Arc::new([]));
                self.obj_table.push(value.clone());
                return Ok(Some(value));
            }
            let obj_idx = self.obj_table.len();
            self.obj_table.push(OcamlValue::Int(0)); // placeholder
            stack.push((tag, obj_idx, size, Vec::with_capacity(size)));
            return Ok(None);
        }

        if code >= PREFIX_SMALL_INT {
            let n = (code & 0x3F) as i64;
            return Ok(Some(OcamlValue::Int(n)));
        }

        if code >= PREFIX_SMALL_STRING {
            let len = (code & 0x1F) as usize;
            let mut buf = vec![0u8; len];
            reader.read_exact(&mut buf)?;
            let s = decode_ocaml_string(&buf);
            let value = self.decoded_string(s);
            self.obj_table.push(value.clone());
            return Ok(Some(value));
        }

        // Explicit opcodes
        match code {
            CODE_INT8 => {
                let n = read_i8(reader)? as i64;
                Ok(Some(OcamlValue::Int(n)))
            }
            CODE_INT16 => {
                let n = read_i16_be(reader)? as i64;
                Ok(Some(OcamlValue::Int(n)))
            }
            CODE_INT32 => {
                let n = read_i32_be(reader)? as i64;
                Ok(Some(OcamlValue::Int(n)))
            }
            CODE_INT64 => {
                let n = read_i64_be(reader)?;
                Ok(Some(OcamlValue::Int(n)))
            }
            CODE_SHARED8 => {
                let distance = read_u8(reader)? as u32;
                Ok(Some(self.resolve_shared(distance)?))
            }
            CODE_SHARED16 => {
                let distance = read_u16_be(reader)? as u32;
                Ok(Some(self.resolve_shared(distance)?))
            }
            CODE_SHARED32 => {
                let distance = read_u32_be(reader)?;
                Ok(Some(self.resolve_shared(distance)?))
            }
            CODE_BLOCK32 => {
                let header = read_u32_be(reader)?;
                let tag = (header & 0xFF) as u8;
                let size = (header >> 10) as usize;
                if size == 0 {
                    let value = OcamlValue::Block(tag, Arc::new([]));
                    self.obj_table.push(value.clone());
                    return Ok(Some(value));
                }
                let obj_idx = self.obj_table.len();
                self.obj_table.push(OcamlValue::Int(0)); // placeholder
                stack.push((tag, obj_idx, size, Vec::with_capacity(size)));
                Ok(None)
            }
            CODE_STRING8 => {
                let len = read_u8(reader)? as usize;
                let mut buf = vec![0u8; len];
                reader.read_exact(&mut buf)?;
                let s = decode_ocaml_string(&buf);
                let value = self.decoded_string(s);
                self.obj_table.push(value.clone());
                Ok(Some(value))
            }
            CODE_STRING32 => {
                let len = read_u32_be(reader)? as usize;
                let mut buf = vec![0u8; len];
                reader.read_exact(&mut buf)?;
                let s = decode_ocaml_string(&buf);
                let value = self.decoded_string(s);
                self.obj_table.push(value.clone());
                Ok(Some(value))
            }
            CODE_DOUBLE_BIG => {
                let bits = read_u64_be(reader)?;
                let f = f64::from_bits(bits);
                let value = OcamlValue::Float(f);
                self.obj_table.push(value.clone());
                Ok(Some(value))
            }
            CODE_DOUBLE_LITTLE => {
                let bits = read_u64_le(reader)?;
                let f = f64::from_bits(bits);
                let value = OcamlValue::Float(f);
                self.obj_table.push(value.clone());
                Ok(Some(value))
            }
            CODE_CUSTOM_FIXED => {
                let id = read_custom_fixed_id(reader)?;
                match id.as_slice() {
                    CUSTOM_INT32_ID => {
                        let value = OcamlValue::Int(read_i32_be(reader)? as i64);
                        self.obj_table.push(value.clone());
                        Ok(Some(value))
                    }
                    _ => Err(MarshalError::BadOpcode(code)),
                }
            }
            _ => Err(MarshalError::BadOpcode(code)),
        }
    }

    /// Resolve a shared reference by distance.
    fn resolve_shared(&self, distance: u32) -> Result<OcamlValue, MarshalError> {
        let current_idx = self.obj_table.len() as u32;
        if distance > current_idx {
            return Err(MarshalError::BadSharedRef(distance));
        }
        let target_idx = (current_idx - distance) as usize;
        if target_idx >= self.obj_table.len() {
            return Err(MarshalError::BadSharedRef(distance));
        }
        Ok(self.obj_table[target_idx].clone())
    }
}

fn decode_ocaml_string(bytes: &[u8]) -> String {
    bytes.iter().map(|&byte| char::from(byte)).collect()
}

// ============================================================================
// IO helpers
// ============================================================================

fn read_u8<R: Read>(reader: &mut R) -> Result<u8, io::Error> {
    let mut buf = [0u8; 1];
    reader.read_exact(&mut buf)?;
    Ok(buf[0])
}

fn read_i8<R: Read>(reader: &mut R) -> Result<i8, io::Error> {
    let mut buf = [0u8; 1];
    reader.read_exact(&mut buf)?;
    Ok(buf[0] as i8)
}

fn read_custom_fixed_id<R: Read>(reader: &mut R) -> Result<Vec<u8>, io::Error> {
    let mut id = Vec::new();
    loop {
        let byte = read_u8(reader)?;
        id.push(byte);
        if byte == 0 {
            return Ok(id);
        }
    }
}

fn read_u16_be<R: Read>(reader: &mut R) -> Result<u16, io::Error> {
    let mut buf = [0u8; 2];
    reader.read_exact(&mut buf)?;
    Ok(u16::from_be_bytes(buf))
}

fn read_i16_be<R: Read>(reader: &mut R) -> Result<i16, io::Error> {
    let mut buf = [0u8; 2];
    reader.read_exact(&mut buf)?;
    Ok(i16::from_be_bytes(buf))
}

fn read_u32_be<R: Read>(reader: &mut R) -> Result<u32, io::Error> {
    let mut buf = [0u8; 4];
    reader.read_exact(&mut buf)?;
    Ok(u32::from_be_bytes(buf))
}

fn read_i32_be<R: Read>(reader: &mut R) -> Result<i32, io::Error> {
    let mut buf = [0u8; 4];
    reader.read_exact(&mut buf)?;
    Ok(i32::from_be_bytes(buf))
}

fn read_u64_be<R: Read>(reader: &mut R) -> Result<u64, io::Error> {
    let mut buf = [0u8; 8];
    reader.read_exact(&mut buf)?;
    Ok(u64::from_be_bytes(buf))
}

fn read_u64_le<R: Read>(reader: &mut R) -> Result<u64, io::Error> {
    let mut buf = [0u8; 8];
    reader.read_exact(&mut buf)?;
    Ok(u64::from_le_bytes(buf))
}

fn read_i64_be<R: Read>(reader: &mut R) -> Result<i64, io::Error> {
    let mut buf = [0u8; 8];
    reader.read_exact(&mut buf)?;
    Ok(i64::from_be_bytes(buf))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decoded_strings_retain_sharing_without_equating_contents() {
        fn allocation(value: &OcamlValue) -> Option<(u64, u32)> {
            let OcamlValue::String(value) = value else {
                panic!("string")
            };
            value.allocation()
        }
        for encoded in [
            vec![0x21, b'x'],
            vec![CODE_STRING8, 1, b'x'],
            vec![CODE_STRING32, 0, 0, 0, 1, b'x'],
            vec![0x20],
        ] {
            let mut payload = vec![0xb0]; // tuple of three strings
            payload.extend(&encoded);
            payload.extend([CODE_SHARED8, 1]);
            payload.extend(&encoded);
            let mut reader = MarshalReader::new();
            let value = reader.read_value(&mut Cursor::new(&payload)).unwrap();
            let (_, fields) = value.as_block();
            assert!(allocation(&fields[0]).is_some());
            assert_eq!(allocation(&fields[0]), allocation(&fields[1]));
            assert_eq!(fields[0].as_string(), fields[2].as_string());
            assert_ne!(allocation(&fields[0]), allocation(&fields[2]));
            assert_eq!(allocation(&fields[0]), allocation(&fields[0].clone()));
            let other = MarshalReader::new()
                .read_value(&mut Cursor::new(&payload))
                .unwrap();
            assert_ne!(allocation(&fields[0]), allocation(&other.as_block().1[0]));

            let mut header = Vec::from(MAGIC_NUMBER_SMALL.to_be_bytes());
            for n in [payload.len() as u32, 3, 0, 0] {
                header.extend(n.to_be_bytes());
            }
            header.extend(&payload);
            let reset = reader.read_from_bytes(&header).unwrap();
            assert_ne!(allocation(&fields[0]), allocation(&reset.as_block().1[0]));
            drop(reader);
            assert_eq!(allocation(&fields[0]), allocation(&fields[1]));
        }
        assert_eq!(allocation(&OcamlValue::String("x".into())), None);
    }

    #[test]
    fn short_debug_truncates_on_char_boundary() {
        // Latin-1 bytes decode to two-byte UTF-8 chars.
        let value = OcamlValue::String("é".repeat(60).into());
        assert_eq!(
            value.short_debug(),
            format!("String(\"{}...\")", "é".repeat(50))
        );
    }

    #[test]
    fn test_read_small_int() {
        // PREFIX_SMALL_INT with value 42: 0x40 + 42 = 0x6A
        let data = [
            0x84, 0x95, 0xA6, 0xBE, // magic
            0x00, 0x00, 0x00, 0x01, // data_len = 1
            0x00, 0x00, 0x00, 0x00, // obj_count = 0
            0x00, 0x00, 0x00, 0x00, // size_32 = 0
            0x00, 0x00, 0x00, 0x00, // size_64 = 0
            0x6A, // PREFIX_SMALL_INT(42)
        ];
        let mut reader = MarshalReader::new();
        let val = reader.read_from_bytes(&data).unwrap();
        assert_eq!(val.as_int(), 42);
    }

    #[test]
    fn test_read_small_string() {
        // PREFIX_SMALL_STRING with length 3: 0x20 + 3 = 0x23
        let data = [
            0x84, 0x95, 0xA6, 0xBE, // magic
            0x00, 0x00, 0x00, 0x04, // data_len = 4
            0x00, 0x00, 0x00, 0x01, // obj_count = 1
            0x00, 0x00, 0x00, 0x00, // size_32
            0x00, 0x00, 0x00, 0x00, // size_64
            0x23, b'f', b'o', b'o', // PREFIX_SMALL_STRING(3) + "foo"
        ];
        let mut reader = MarshalReader::new();
        let val = reader.read_from_bytes(&data).unwrap();
        assert_eq!(val.as_string(), "foo");
    }

    #[test]
    fn test_read_small_string_preserves_non_utf8_bytes() {
        let data = [
            0x84, 0x95, 0xA6, 0xBE, // magic
            0x00, 0x00, 0x00, 0x02, // data_len = 2
            0x00, 0x00, 0x00, 0x01, // obj_count = 1
            0x00, 0x00, 0x00, 0x00, // size_32
            0x00, 0x00, 0x00, 0x00, // size_64
            0x21, 0x84, // PREFIX_SMALL_STRING(1) + raw byte 0x84
        ];
        let mut reader = MarshalReader::new();
        let val = reader.read_from_bytes(&data).unwrap();
        assert_eq!(val.as_string().chars().next().unwrap() as u32 as u8, 0x84);
    }

    #[test]
    fn test_read_small_block() {
        // Block(tag=0, size=2) containing Int(1) and Int(2)
        // PREFIX_SMALL_BLOCK: 0x80 + (2 << 4) + 0 = 0x80 + 0x20 = 0xA0
        let data = [
            0x84, 0x95, 0xA6, 0xBE, // magic
            0x00, 0x00, 0x00, 0x03, // data_len = 3
            0x00, 0x00, 0x00, 0x01, // obj_count = 1
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0xA0, // PREFIX_SMALL_BLOCK(tag=0, size=2)
            0x41, // PREFIX_SMALL_INT(1)
            0x42, // PREFIX_SMALL_INT(2)
        ];
        let mut reader = MarshalReader::new();
        let val = reader.read_from_bytes(&data).unwrap();
        let (tag, fields) = val.as_block();
        assert_eq!(tag, 0);
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].as_int(), 1);
        assert_eq!(fields[1].as_int(), 2);
    }

    #[test]
    fn test_read_custom_fixed_int32() {
        let data = [
            0x84,
            0x95,
            0xA6,
            0xBE, // magic
            0x00,
            0x00,
            0x00,
            0x08, // data_len = 8
            0x00,
            0x00,
            0x00,
            0x01, // obj_count = 1
            0x00,
            0x00,
            0x00,
            0x03, // size_32 = 3 words
            0x00,
            0x00,
            0x00,
            0x03, // size_64 = 3 words
            CODE_CUSTOM_FIXED,
            b'_',
            b'i',
            0x00,
            0x00,
            0x00,
            0x00,
            0x01,
        ];
        let mut reader = MarshalReader::new();
        let val = reader.read_from_bytes(&data).unwrap();
        assert_eq!(val.as_int(), 1);
    }
}
