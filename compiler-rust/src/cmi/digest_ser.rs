//! A serde `Serializer` that feeds a value into a hasher in canonical form,
//! for interface digests: what dependents' compiles read of a value, and
//! nothing else.
//!
//! - Source locations (`Location`, `Position`) and the handles and tables
//!   that stand for them (`LamLoc`, `DeclLoc`, `DeclLocTable`) are skipped:
//!   moving code does not change what dependents compile. Handles number
//!   locations in allocation order, so they shift when code is added above.
//! - Local identifiers are numbered in order of first appearance instead of
//!   by stamp: stamps come from a per-compile counter, so the same code gets
//!   different stamps depending on what was compiled before it.
//!   Persistent identifiers (stamp 0) are kept by name.

use serde::ser::{self, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::hash::Hasher;

/// A serialization error. Canonical hashing never produces one; serde's
/// `Serializer` trait requires the type.
#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

impl ser::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error(msg.to_string())
    }
}

type Result<T> = std::result::Result<T, Error>;

/// Feed `value` into `hasher` in canonical form. Identifier numbering is
/// shared by all values hashed with the same `Canonical`.
pub struct Canonical<'h, H: Hasher> {
    hasher: &'h mut H,
    stamps: HashMap<i32, u32>,
}

impl<'h, H: Hasher> Canonical<'h, H> {
    /// Start hashing into `hasher`, with no identifiers numbered yet.
    pub fn new(hasher: &'h mut H) -> Self {
        Canonical {
            hasher,
            stamps: HashMap::new(),
        }
    }

    /// Feed `value` into the hasher, numbering its local identifiers after
    /// those of the values hashed before it.
    pub fn hash<T: Serialize + ?Sized>(&mut self, value: &T) {
        // Hashing cannot fail: every serializer method below succeeds, and
        // identifier stamps are always integers.
        let result = value.serialize(&mut *self);
        debug_assert!(result.is_ok(), "canonical hashing failed: {result:?}");
    }

    fn tag(&mut self, tag: u8) {
        self.hasher.write_u8(tag);
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.hasher.write_usize(bytes.len());
        self.hasher.write(bytes);
    }

    fn stamp(&mut self, stamp: i32) {
        if stamp == 0 {
            self.hasher.write_i32(0);
            return;
        }
        let next = self.stamps.len() as u32 + 1;
        let canonical = *self.stamps.entry(stamp).or_insert(next);
        self.hasher.write_u32(canonical);
    }
}

/// How the fields of a struct being serialized are hashed.
enum Fields {
    /// Every field, in order.
    All,
    /// None: a location.
    Skip,
    /// An identifier: its stamp is canonicalized.
    Ident,
}

/// The serializer of a sequence, tuple, map or struct being hashed.
pub struct Compound<'a, 'h, H: Hasher> {
    ser: &'a mut Canonical<'h, H>,
    fields: Fields,
}

impl<'a, 'h, H: Hasher> ser::Serializer for &'a mut Canonical<'h, H> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Compound<'a, 'h, H>;
    type SerializeTuple = Compound<'a, 'h, H>;
    type SerializeTupleStruct = Compound<'a, 'h, H>;
    type SerializeTupleVariant = Compound<'a, 'h, H>;
    type SerializeMap = Compound<'a, 'h, H>;
    type SerializeStruct = Compound<'a, 'h, H>;
    type SerializeStructVariant = Compound<'a, 'h, H>;

    fn serialize_bool(self, v: bool) -> Result<()> {
        self.tag(1);
        self.hasher.write_u8(v as u8);
        Ok(())
    }
    fn serialize_i8(self, v: i8) -> Result<()> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i16(self, v: i16) -> Result<()> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i32(self, v: i32) -> Result<()> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i64(self, v: i64) -> Result<()> {
        self.tag(2);
        self.hasher.write_i64(v);
        Ok(())
    }
    fn serialize_i128(self, v: i128) -> Result<()> {
        self.tag(3);
        self.hasher.write_i128(v);
        Ok(())
    }
    fn serialize_u8(self, v: u8) -> Result<()> {
        self.serialize_u64(v as u64)
    }
    fn serialize_u16(self, v: u16) -> Result<()> {
        self.serialize_u64(v as u64)
    }
    fn serialize_u32(self, v: u32) -> Result<()> {
        self.serialize_u64(v as u64)
    }
    fn serialize_u64(self, v: u64) -> Result<()> {
        self.tag(4);
        self.hasher.write_u64(v);
        Ok(())
    }
    fn serialize_u128(self, v: u128) -> Result<()> {
        self.tag(5);
        self.hasher.write_u128(v);
        Ok(())
    }
    fn serialize_f32(self, v: f32) -> Result<()> {
        self.serialize_f64(v as f64)
    }
    fn serialize_f64(self, v: f64) -> Result<()> {
        self.tag(6);
        self.hasher.write_u64(v.to_bits());
        Ok(())
    }
    fn serialize_char(self, v: char) -> Result<()> {
        self.tag(7);
        self.hasher.write_u32(v as u32);
        Ok(())
    }
    fn serialize_str(self, v: &str) -> Result<()> {
        self.tag(8);
        self.bytes(v.as_bytes());
        Ok(())
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        self.tag(9);
        self.bytes(v);
        Ok(())
    }
    fn serialize_none(self) -> Result<()> {
        self.tag(10);
        Ok(())
    }
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<()> {
        self.tag(11);
        value.serialize(self)
    }
    fn serialize_unit(self) -> Result<()> {
        self.tag(12);
        Ok(())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        self.serialize_unit()
    }
    fn serialize_unit_variant(self, _: &'static str, index: u32, _: &'static str) -> Result<()> {
        self.tag(13);
        self.hasher.write_u32(index);
        Ok(())
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        value: &T,
    ) -> Result<()> {
        value.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        index: u32,
        _: &'static str,
        value: &T,
    ) -> Result<()> {
        self.tag(14);
        self.hasher.write_u32(index);
        value.serialize(self)
    }
    fn serialize_seq(self, len: Option<usize>) -> Result<Compound<'a, 'h, H>> {
        self.tag(15);
        if let Some(len) = len {
            self.hasher.write_usize(len);
        }
        Ok(Compound {
            ser: self,
            fields: Fields::All,
        })
    }
    fn serialize_tuple(self, _: usize) -> Result<Compound<'a, 'h, H>> {
        self.tag(16);
        Ok(Compound {
            ser: self,
            fields: Fields::All,
        })
    }
    fn serialize_tuple_struct(self, _: &'static str, _: usize) -> Result<Compound<'a, 'h, H>> {
        self.serialize_tuple(0)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        index: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Compound<'a, 'h, H>> {
        self.tag(17);
        self.hasher.write_u32(index);
        Ok(Compound {
            ser: self,
            fields: Fields::All,
        })
    }
    fn serialize_map(self, len: Option<usize>) -> Result<Compound<'a, 'h, H>> {
        self.serialize_seq(len)
    }
    fn serialize_struct(self, name: &'static str, _: usize) -> Result<Compound<'a, 'h, H>> {
        let fields = match name {
            // Location handles and their tables number locations in
            // allocation order; cache validity must not depend on that.
            "Location" | "Position" | "LamLoc" | "DeclLoc" | "DeclLocTable" => Fields::Skip,
            "Ident" => Fields::Ident,
            _ => {
                self.tag(18);
                Fields::All
            }
        };
        Ok(Compound { ser: self, fields })
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        index: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Compound<'a, 'h, H>> {
        self.serialize_tuple_variant("", index, "", 0)
    }
}

impl<H: Hasher> Compound<'_, '_, H> {
    fn element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        value.serialize(&mut *self.ser)
    }
}

macro_rules! elements {
    ($($trait:ident :: $method:ident),*) => {$(
        impl<H: Hasher> ser::$trait for Compound<'_, '_, H> {
            type Ok = ();
            type Error = Error;
            fn $method<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
                self.element(value)
            }
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    )*};
}

elements!(
    SerializeSeq::serialize_element,
    SerializeTuple::serialize_element,
    SerializeTupleStruct::serialize_field,
    SerializeTupleVariant::serialize_field
);

impl<H: Hasher> ser::SerializeMap for Compound<'_, '_, H> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<()> {
        self.element(key)
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        self.element(value)
    }
    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<H: Hasher> ser::SerializeStruct for Compound<'_, '_, H> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<()> {
        match self.fields {
            Fields::Skip => Ok(()),
            Fields::All => self.element(value),
            Fields::Ident if key == "stamp" => {
                let stamp = value.serialize(StampOf)?;
                self.ser.stamp(stamp);
                Ok(())
            }
            Fields::Ident => self.element(value),
        }
    }
    fn end(self) -> Result<()> {
        Ok(())
    }
}

impl<H: Hasher> ser::SerializeStructVariant for Compound<'_, '_, H> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: Serialize + ?Sized>(&mut self, _: &'static str, value: &T) -> Result<()> {
        self.element(value)
    }
    fn end(self) -> Result<()> {
        Ok(())
    }
}

/// Reads an identifier's stamp (an `i32`).
struct StampOf;

impl ser::Serializer for StampOf {
    type Ok = i32;
    type Error = Error;
    type SerializeSeq = ser::Impossible<i32, Error>;
    type SerializeTuple = ser::Impossible<i32, Error>;
    type SerializeTupleStruct = ser::Impossible<i32, Error>;
    type SerializeTupleVariant = ser::Impossible<i32, Error>;
    type SerializeMap = ser::Impossible<i32, Error>;
    type SerializeStruct = ser::Impossible<i32, Error>;
    type SerializeStructVariant = ser::Impossible<i32, Error>;

    fn serialize_i32(self, v: i32) -> Result<i32> {
        Ok(v)
    }
    fn serialize_bool(self, _: bool) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_i8(self, v: i8) -> Result<i32> {
        Ok(v as i32)
    }
    fn serialize_i16(self, v: i16) -> Result<i32> {
        Ok(v as i32)
    }
    fn serialize_i64(self, v: i64) -> Result<i32> {
        i32::try_from(v).map_err(|_| not_a_stamp())
    }
    fn serialize_u8(self, v: u8) -> Result<i32> {
        Ok(v as i32)
    }
    fn serialize_u16(self, v: u16) -> Result<i32> {
        Ok(v as i32)
    }
    fn serialize_u32(self, v: u32) -> Result<i32> {
        i32::try_from(v).map_err(|_| not_a_stamp())
    }
    fn serialize_u64(self, v: u64) -> Result<i32> {
        i32::try_from(v).map_err(|_| not_a_stamp())
    }
    fn serialize_f32(self, _: f32) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_f64(self, _: f64) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_char(self, _: char) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_str(self, _: &str) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_bytes(self, _: &[u8]) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_none(self) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_some<T: Serialize + ?Sized>(self, _: &T) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_unit(self) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_unit_variant(self, _: &'static str, _: u32, _: &'static str) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        value: &T,
    ) -> Result<i32> {
        value.serialize(self)
    }
    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: &T,
    ) -> Result<i32> {
        Err(not_a_stamp())
    }
    fn serialize_seq(self, _: Option<usize>) -> Result<Self::SerializeSeq> {
        Err(not_a_stamp())
    }
    fn serialize_tuple(self, _: usize) -> Result<Self::SerializeTuple> {
        Err(not_a_stamp())
    }
    fn serialize_tuple_struct(
        self,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        Err(not_a_stamp())
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        Err(not_a_stamp())
    }
    fn serialize_map(self, _: Option<usize>) -> Result<Self::SerializeMap> {
        Err(not_a_stamp())
    }
    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self::SerializeStruct> {
        Err(not_a_stamp())
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        _: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self::SerializeStructVariant> {
        Err(not_a_stamp())
    }
}

fn not_a_stamp() -> Error {
    Error("an identifier stamp is an i32".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::location::Location;

    #[derive(serde::Serialize)]
    struct Node {
        loc: Location,
        id: Ident,
        other: Ident,
        global: Ident,
        value: i64,
    }

    fn digest(node: &Node) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        Canonical::new(&mut hasher).hash(node);
        hasher.finish()
    }

    fn node(stamps: (i32, i32), line: i32, value: i64) -> Node {
        let mut loc = Location::none();
        loc.loc_start.line = line;
        Node {
            loc,
            id: Ident::new("x", stamps.0, IdentFlags::default()),
            other: Ident::new("y", stamps.1, IdentFlags::default()),
            global: Ident::new("Global", 0, IdentFlags::default()),
            value,
        }
    }

    #[derive(serde::Serialize)]
    struct WithHandle {
        loc: crate::lambda::LamLoc,
        value: i64,
    }

    #[test]
    fn location_handles_do_not_count() {
        let digest = |node: &WithHandle| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            Canonical::new(&mut hasher).hash(node);
            hasher.finish()
        };
        let a = digest(&WithHandle {
            loc: crate::lambda::LamLoc::for_test(0),
            value: 5,
        });
        assert_eq!(
            a,
            digest(&WithHandle {
                loc: crate::lambda::LamLoc::for_test(7),
                value: 5
            })
        );
        assert_eq!(
            a,
            digest(&WithHandle {
                loc: crate::lambda::LamLoc::NONE,
                value: 5
            })
        );
        assert_ne!(
            a,
            digest(&WithHandle {
                loc: crate::lambda::LamLoc::NONE,
                value: 6
            })
        );
    }

    #[test]
    fn declaration_location_handles_do_not_count() {
        #[derive(serde::Serialize)]
        struct Decl {
            loc: crate::types::DeclLoc,
            table: crate::types::DeclLocTable,
            value: i64,
        }
        let hash = |decl: &Decl| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            Canonical::new(&mut hasher).hash(decl);
            hasher.finish()
        };
        let mut located = crate::types::DeclLocTable::default();
        let mut loc = Location::none();
        loc.loc_start.line = 4;
        let handle = located.intern(loc);
        let a = Decl {
            loc: handle,
            table: located,
            value: 1,
        };
        let b = Decl {
            loc: crate::types::DeclLoc::none(),
            table: Default::default(),
            value: 1,
        };
        assert_eq!(hash(&a), hash(&b));
        assert_ne!(hash(&a), hash(&Decl { value: 2, ..b }));
    }

    #[test]
    fn locations_and_stamp_numbering_do_not_count() {
        let a = digest(&node((10, 11), 1, 5));
        assert_eq!(a, digest(&node((70, 71), 9, 5)));
        // Which identifiers are the same still counts.
        assert_ne!(a, digest(&node((10, 10), 1, 5)));
        assert_ne!(a, digest(&node((10, 11), 1, 6)));
    }
}
