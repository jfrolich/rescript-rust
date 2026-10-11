//! A compact, non-self-describing binary serde format (bincode-like), for
//! data this compiler writes and reads back itself: integers as LEB128
//! varints (signed ones zigzag-encoded), strings and sequences
//! length-prefixed, structs as their fields in order, enum variants by index.
//! Deserializing needs the exact type that was serialized.

use serde::de::{self, DeserializeSeed, IntoDeserializer, Visitor};
use serde::ser::{self, Serialize};
use std::fmt;

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

impl de::Error for Error {
    fn custom<T: fmt::Display>(msg: T) -> Self {
        Error(msg.to_string())
    }
}

type Result<T> = std::result::Result<T, Error>;

/// Serialize `value`.
pub fn to_vec<T: Serialize + ?Sized>(value: &T) -> Result<Vec<u8>> {
    let mut serializer = Serializer { out: Vec::new() };
    value.serialize(&mut serializer)?;
    Ok(serializer.out)
}

/// Deserialize a `T` from all of `bytes`.
pub fn from_slice<'de, T: de::Deserialize<'de>>(bytes: &'de [u8]) -> Result<T> {
    let mut deserializer = Deserializer { input: bytes };
    let value = T::deserialize(&mut deserializer)?;
    if !deserializer.input.is_empty() {
        return Err(Error("trailing bytes".to_string()));
    }
    Ok(value)
}

pub struct Serializer {
    out: Vec<u8>,
}

impl Serializer {
    fn varint(&mut self, mut value: u64) {
        while value >= 0x80 {
            self.out.push((value as u8) | 0x80);
            value >>= 7;
        }
        self.out.push(value as u8);
    }

    fn signed(&mut self, value: i64) {
        self.varint(((value << 1) ^ (value >> 63)) as u64);
    }
}

/// Collects a sequence or map whose length is not known up front.
pub struct Compound<'a> {
    ser: &'a mut Serializer,
    /// For unknown lengths: where the elements start, and how many.
    buffered: Option<(Vec<u8>, u64)>,
}

impl Compound<'_> {
    fn element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        value.serialize(&mut *self.ser)?;
        if let Some((_, count)) = &mut self.buffered {
            *count += 1;
        }
        Ok(())
    }

    fn finish(self) -> Result<()> {
        if let Some((outer, count)) = self.buffered {
            let elements = std::mem::replace(&mut self.ser.out, outer);
            self.ser.varint(count);
            self.ser.out.extend_from_slice(&elements);
        }
        Ok(())
    }
}

fn compound(ser: &mut Serializer, len: Option<usize>) -> Compound<'_> {
    match len {
        Some(len) => {
            ser.varint(len as u64);
            Compound {
                ser,
                buffered: None,
            }
        }
        None => {
            let outer = std::mem::take(&mut ser.out);
            Compound {
                ser,
                buffered: Some((outer, 0)),
            }
        }
    }
}

impl<'a> ser::Serializer for &'a mut Serializer {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Compound<'a>;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Compound<'a>;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn serialize_bool(self, v: bool) -> Result<()> {
        self.out.push(v as u8);
        Ok(())
    }
    fn serialize_i8(self, v: i8) -> Result<()> {
        self.signed(v as i64);
        Ok(())
    }
    fn serialize_i16(self, v: i16) -> Result<()> {
        self.signed(v as i64);
        Ok(())
    }
    fn serialize_i32(self, v: i32) -> Result<()> {
        self.signed(v as i64);
        Ok(())
    }
    fn serialize_i64(self, v: i64) -> Result<()> {
        self.signed(v);
        Ok(())
    }
    fn serialize_i128(self, v: i128) -> Result<()> {
        self.out.extend_from_slice(&v.to_le_bytes());
        Ok(())
    }
    fn serialize_u8(self, v: u8) -> Result<()> {
        self.varint(v as u64);
        Ok(())
    }
    fn serialize_u16(self, v: u16) -> Result<()> {
        self.varint(v as u64);
        Ok(())
    }
    fn serialize_u32(self, v: u32) -> Result<()> {
        self.varint(v as u64);
        Ok(())
    }
    fn serialize_u64(self, v: u64) -> Result<()> {
        self.varint(v);
        Ok(())
    }
    fn serialize_u128(self, v: u128) -> Result<()> {
        self.out.extend_from_slice(&v.to_le_bytes());
        Ok(())
    }
    fn serialize_f32(self, v: f32) -> Result<()> {
        self.out.extend_from_slice(&v.to_le_bytes());
        Ok(())
    }
    fn serialize_f64(self, v: f64) -> Result<()> {
        self.out.extend_from_slice(&v.to_le_bytes());
        Ok(())
    }
    fn serialize_char(self, v: char) -> Result<()> {
        self.varint(v as u64);
        Ok(())
    }
    fn serialize_str(self, v: &str) -> Result<()> {
        self.serialize_bytes(v.as_bytes())
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<()> {
        self.varint(v.len() as u64);
        self.out.extend_from_slice(v);
        Ok(())
    }
    fn serialize_none(self) -> Result<()> {
        self.out.push(0);
        Ok(())
    }
    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<()> {
        self.out.push(1);
        value.serialize(self)
    }
    fn serialize_unit(self) -> Result<()> {
        Ok(())
    }
    fn serialize_unit_struct(self, _: &'static str) -> Result<()> {
        Ok(())
    }
    fn serialize_unit_variant(self, _: &'static str, index: u32, _: &'static str) -> Result<()> {
        self.varint(index as u64);
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
        self.varint(index as u64);
        value.serialize(self)
    }
    fn serialize_seq(self, len: Option<usize>) -> Result<Compound<'a>> {
        Ok(compound(self, len))
    }
    fn serialize_tuple(self, _: usize) -> Result<Self> {
        Ok(self)
    }
    fn serialize_tuple_struct(self, _: &'static str, _: usize) -> Result<Self> {
        Ok(self)
    }
    fn serialize_tuple_variant(
        self,
        _: &'static str,
        index: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self> {
        self.varint(index as u64);
        Ok(self)
    }
    fn serialize_map(self, len: Option<usize>) -> Result<Compound<'a>> {
        Ok(compound(self, len))
    }
    fn serialize_struct(self, _: &'static str, _: usize) -> Result<Self> {
        Ok(self)
    }
    fn serialize_struct_variant(
        self,
        _: &'static str,
        index: u32,
        _: &'static str,
        _: usize,
    ) -> Result<Self> {
        self.varint(index as u64);
        Ok(self)
    }
}

impl ser::SerializeSeq for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        self.element(value)
    }
    fn end(self) -> Result<()> {
        self.finish()
    }
}

impl ser::SerializeMap for Compound<'_> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<()> {
        // Counted once per entry, on the key.
        self.element(key)
    }
    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<()> {
        value.serialize(&mut *self.ser)
    }
    fn end(self) -> Result<()> {
        self.finish()
    }
}

macro_rules! fields {
    ($trait:ident, $method:ident $(, $key:ident)?) => {
        impl ser::$trait for &mut Serializer {
            type Ok = ();
            type Error = Error;
            fn $method<T: Serialize + ?Sized>(&mut self, $($key: &'static str,)? value: &T) -> Result<()> {
                $(let _ = $key;)?
                value.serialize(&mut **self)
            }
            fn end(self) -> Result<()> {
                Ok(())
            }
        }
    };
}

fields!(SerializeTuple, serialize_element);
fields!(SerializeTupleStruct, serialize_field);
fields!(SerializeTupleVariant, serialize_field);
fields!(SerializeStruct, serialize_field, _key);
fields!(SerializeStructVariant, serialize_field, _key);

pub struct Deserializer<'de> {
    input: &'de [u8],
}

impl<'de> Deserializer<'de> {
    fn byte(&mut self) -> Result<u8> {
        let (&first, rest) = self
            .input
            .split_first()
            .ok_or_else(|| Error("unexpected end".to_string()))?;
        self.input = rest;
        Ok(first)
    }

    fn take(&mut self, len: usize) -> Result<&'de [u8]> {
        if self.input.len() < len {
            return Err(Error("unexpected end".to_string()));
        }
        let (taken, rest) = self.input.split_at(len);
        self.input = rest;
        Ok(taken)
    }

    fn varint(&mut self) -> Result<u64> {
        let mut value = 0u64;
        let mut shift = 0;
        loop {
            let byte = self.byte()?;
            value |= ((byte & 0x7f) as u64) << shift;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
            shift += 7;
            if shift > 63 {
                return Err(Error("varint too long".to_string()));
            }
        }
    }

    fn signed(&mut self) -> Result<i64> {
        let value = self.varint()?;
        Ok(((value >> 1) as i64) ^ -((value & 1) as i64))
    }

    fn len(&mut self) -> Result<usize> {
        let len = self.varint()? as usize;
        // Every element takes at least a byte, except for zero-sized ones;
        // a bound against corrupt input.
        if len > self.input.len().max(1) * 64 {
            return Err(Error("length out of range".to_string()));
        }
        Ok(len)
    }

    fn bytes(&mut self) -> Result<&'de [u8]> {
        let len = self.varint()? as usize;
        self.take(len)
    }

    fn fixed<const N: usize>(&mut self) -> Result<[u8; N]> {
        let mut out = [0; N];
        out.copy_from_slice(self.take(N)?);
        Ok(out)
    }
}

fn overflow() -> Error {
    Error("integer out of range".to_string())
}

impl<'de> de::Deserializer<'de> for &mut Deserializer<'de> {
    type Error = Error;

    fn deserialize_any<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        Err(Error("the format is not self-describing".to_string()))
    }
    fn deserialize_bool<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_bool(self.byte()? != 0)
    }
    fn deserialize_i8<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_i8(self.signed()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_i16<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_i16(self.signed()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_i32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_i32(self.signed()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_i64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_i64(self.signed()?)
    }
    fn deserialize_i128<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_i128(i128::from_le_bytes(self.fixed()?))
    }
    fn deserialize_u8<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u8(self.varint()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_u16<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u16(self.varint()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_u32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u32(self.varint()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_u64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u64(self.varint()?)
    }
    fn deserialize_u128<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u128(u128::from_le_bytes(self.fixed()?))
    }
    fn deserialize_f32<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_f32(f32::from_le_bytes(self.fixed()?))
    }
    fn deserialize_f64<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_f64(f64::from_le_bytes(self.fixed()?))
    }
    fn deserialize_char<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let code: u32 = self.varint()?.try_into().map_err(|_| overflow())?;
        visitor.visit_char(char::from_u32(code).ok_or_else(|| Error("invalid char".to_string()))?)
    }
    fn deserialize_str<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let bytes = self.bytes()?;
        visitor.visit_borrowed_str(
            std::str::from_utf8(bytes).map_err(|_| Error("invalid utf-8".to_string()))?,
        )
    }
    fn deserialize_string<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.deserialize_str(visitor)
    }
    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_borrowed_bytes(self.bytes()?)
    }
    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        self.deserialize_bytes(visitor)
    }
    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        match self.byte()? {
            0 => visitor.visit_none(),
            _ => visitor.visit_some(self),
        }
    }
    fn deserialize_unit<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_unit()
    }
    fn deserialize_unit_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_unit()
    }
    fn deserialize_newtype_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_newtype_struct(self)
    }
    fn deserialize_seq<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let len = self.len()?;
        visitor.visit_seq(Elements {
            de: self,
            left: len,
        })
    }
    fn deserialize_tuple<V: Visitor<'de>>(self, len: usize, visitor: V) -> Result<V::Value> {
        visitor.visit_seq(Elements {
            de: self,
            left: len,
        })
    }
    fn deserialize_tuple_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_seq(Elements {
            de: self,
            left: len,
        })
    }
    fn deserialize_map<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        let len = self.len()?;
        visitor.visit_map(Elements {
            de: self,
            left: len,
        })
    }
    fn deserialize_struct<V: Visitor<'de>>(
        self,
        _: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_seq(Elements {
            de: self,
            left: fields.len(),
        })
    }
    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _: &'static str,
        _: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_enum(self)
    }
    fn deserialize_identifier<V: Visitor<'de>>(self, visitor: V) -> Result<V::Value> {
        visitor.visit_u32(self.varint()?.try_into().map_err(|_| overflow())?)
    }
    fn deserialize_ignored_any<V: Visitor<'de>>(self, _: V) -> Result<V::Value> {
        Err(Error("the format is not self-describing".to_string()))
    }
    fn is_human_readable(&self) -> bool {
        false
    }
}

struct Elements<'a, 'de> {
    de: &'a mut Deserializer<'de>,
    left: usize,
}

impl<'de> de::SeqAccess<'de> for Elements<'_, 'de> {
    type Error = Error;
    fn next_element_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> Result<Option<T::Value>> {
        if self.left == 0 {
            return Ok(None);
        }
        self.left -= 1;
        seed.deserialize(&mut *self.de).map(Some)
    }
    fn size_hint(&self) -> Option<usize> {
        Some(self.left)
    }
}

impl<'de> de::MapAccess<'de> for Elements<'_, 'de> {
    type Error = Error;
    fn next_key_seed<K: DeserializeSeed<'de>>(&mut self, seed: K) -> Result<Option<K::Value>> {
        if self.left == 0 {
            return Ok(None);
        }
        self.left -= 1;
        seed.deserialize(&mut *self.de).map(Some)
    }
    fn next_value_seed<V: DeserializeSeed<'de>>(&mut self, seed: V) -> Result<V::Value> {
        seed.deserialize(&mut *self.de)
    }
    fn size_hint(&self) -> Option<usize> {
        Some(self.left)
    }
}

impl<'de> de::EnumAccess<'de> for &mut Deserializer<'de> {
    type Error = Error;
    type Variant = Self;
    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> Result<(V::Value, Self)> {
        let index: u32 = self.varint()?.try_into().map_err(|_| overflow())?;
        let value = seed.deserialize(index.into_deserializer())?;
        Ok((value, self))
    }
}

impl<'de> de::VariantAccess<'de> for &mut Deserializer<'de> {
    type Error = Error;
    fn unit_variant(self) -> Result<()> {
        Ok(())
    }
    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, seed: T) -> Result<T::Value> {
        seed.deserialize(self)
    }
    fn tuple_variant<V: Visitor<'de>>(self, len: usize, visitor: V) -> Result<V::Value> {
        visitor.visit_seq(Elements {
            de: self,
            left: len,
        })
    }
    fn struct_variant<V: Visitor<'de>>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value> {
        visitor.visit_seq(Elements {
            de: self,
            left: fields.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[derive(Debug, PartialEq, serde::Serialize, serde::Deserialize)]
    enum Shape {
        Unit,
        Newtype(i64),
        Tuple(u8, String),
        Struct { name: String, sides: Option<u32> },
    }

    #[derive(Debug, PartialEq, serde::Serialize, serde::Deserialize)]
    struct Value {
        flag: bool,
        small: i32,
        big: u64,
        float: f64,
        text: String,
        shapes: Vec<Shape>,
        map: BTreeMap<String, (i8, Option<char>)>,
        shared: std::sync::Arc<str>,
    }

    #[test]
    fn values_round_trip() {
        let value = Value {
            flag: true,
            small: -300,
            big: u64::MAX,
            float: 1.5,
            text: "héllo".to_string(),
            shapes: vec![
                Shape::Unit,
                Shape::Newtype(i64::MIN),
                Shape::Tuple(7, "x".to_string()),
                Shape::Struct {
                    name: "n".to_string(),
                    sides: Some(4),
                },
            ],
            map: [
                ("a".to_string(), (-1, Some('z'))),
                ("b".to_string(), (2, None)),
            ]
            .into_iter()
            .collect(),
            shared: "shared".into(),
        };
        let bytes = to_vec(&value).unwrap();
        assert_eq!(from_slice::<Value>(&bytes).unwrap(), value);
        assert!(from_slice::<Value>(&bytes[..bytes.len() - 1]).is_err());
    }

    #[test]
    fn unknown_lengths_are_counted() {
        struct Iter;
        impl Serialize for Iter {
            fn serialize<S: ser::Serializer>(
                &self,
                serializer: S,
            ) -> std::result::Result<S::Ok, S::Error> {
                serializer.collect_seq((0..3u32).filter(|n| n % 2 == 0))
            }
        }
        let bytes = to_vec(&Iter).unwrap();
        assert_eq!(from_slice::<Vec<u32>>(&bytes).unwrap(), vec![0, 2]);
    }
}
