use std::collections::HashMap;

use miette::Diagnostic;
use serde::de::{self, DeserializeOwned, IntoDeserializer, Visitor};

use crate::{deserialize, eval::Value, run};

pub fn from_str<T>(source: &str) -> Result<T, miette::Error>
where
    T: DeserializeOwned,
{
    let value = run(source)?;
    let deserializer = deserialize::Deserializer::new(value);
    Ok(T::deserialize(deserializer)?)
}

#[derive(Diagnostic, Debug, PartialEq)]
#[diagnostic()]
pub enum Error {
    Message(String),
}

impl serde::de::Error for Error {
    fn custom<T: std::fmt::Display>(msg: T) -> Self {
        Error::Message(msg.to_string())
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Message(msg) => formatter.write_str(msg),
        }
    }
}

impl std::error::Error for Error {}

pub struct Deserializer<'de> {
    value: Value,
    phantom: std::marker::PhantomData<&'de ()>,
}

impl<'de> Deserializer<'de> {
    pub fn new(value: Value) -> Self {
        Deserializer {
            value,
            phantom: std::marker::PhantomData,
        }
    }
}

impl<'de, 'a> de::Deserializer<'de> for Deserializer<'a> {
    type Error = Error;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_f64(n),
            Value::String(s) => visitor.visit_string(s),
            Value::Struct(_name, map) => {
                let map_deserializer = MapDeserializer::new(map);
                visitor.visit_map(map_deserializer)
            }
            Value::List(l) => {
                let seq_deserializer = SeqDeserializer::new(l);
                visitor.visit_seq(seq_deserializer)
            }
            Value::Unit => visitor.visit_unit(),
            _ => Err(de::Error::custom(format!(
                "unsupported Value type for deserialization: {:?}",
                self.value
            ))),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_bool(n != 0.0),
            _ => Err(de::Error::custom("expected a boolean")),
        }
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_i8(n as i8),
            _ => Err(de::Error::custom("expected an i8")),
        }
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_i16(n as i16),
            _ => Err(de::Error::custom("expected an i16")),
        }
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_i32(n as i32),
            _ => Err(de::Error::custom("expected an i32")),
        }
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_i64(n as i64),
            _ => Err(de::Error::custom("expected an i64")),
        }
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_u8(n as u8),
            _ => Err(de::Error::custom("expected a u8")),
        }
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_u16(n as u16),
            _ => Err(de::Error::custom("expected a u16")),
        }
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_u32(n as u32),
            _ => Err(de::Error::custom("expected a u32")),
        }
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_u64(n as u64),
            _ => Err(de::Error::custom("expected a u64")),
        }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_f32(n as f32),
            _ => Err(de::Error::custom("expected an f32")),
        }
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Number(n) => visitor.visit_f64(n),
            _ => Err(de::Error::custom("expected an f64")),
        }
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::String(s) => visitor.visit_string(s),
            _ => Err(de::Error::custom("expected a string")),
        }
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_byte_buf(visitor)
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::String(s) => visitor.visit_bytes(s.as_bytes()),
            _ => Err(de::Error::custom("expected a byte buffer")),
        }
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Unit => visitor.visit_none(),
            _ => visitor.visit_some(self),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Unit => visitor.visit_unit(),
            _ => Err(de::Error::custom("expected unit")),
        }
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Unit => visitor.visit_unit(),
            _ => Err(de::Error::custom("expected unit struct")),
        }
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::List(l) => {
                let seq_deserializer = SeqDeserializer::new(l);
                visitor.visit_seq(seq_deserializer)
            }
            _ => Err(de::Error::custom("expected a list")),
        }
    }

    fn deserialize_tuple<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(de::Error::custom("tuples are not supported"))
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(de::Error::custom("tuple structs are not supported"))
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        match self.value {
            Value::Struct(_name, map) => {
                let map_deserializer = MapDeserializer::new(map);
                visitor.visit_map(map_deserializer)
            }
            _ => Err(de::Error::custom("expected a map")),
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(de::Error::custom("enums are not supported"))
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

struct MapDeserializer<'de> {
    iter: std::collections::hash_map::IntoIter<String, Value>,
    next_value: Option<Value>,
    phantom: std::marker::PhantomData<&'de ()>,
}

impl<'de> MapDeserializer<'de> {
    fn new(map: HashMap<String, Value>) -> Self {
        MapDeserializer {
            iter: map.into_iter(),
            next_value: None,
            phantom: std::marker::PhantomData,
        }
    }
}

impl<'de> de::MapAccess<'de> for MapDeserializer<'de> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: de::DeserializeSeed<'de>,
    {
        if let Some((key, value)) = self.iter.next() {
            self.next_value = Some(value);
            seed.deserialize(key.into_deserializer()).map(Some)
        } else {
            Ok(None)
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: de::DeserializeSeed<'de>,
    {
        let value = self
            .next_value
            .take()
            .ok_or_else(|| de::Error::custom("unexpected end of map"))?;
        seed.deserialize(Deserializer::new(value))
    }
}

struct SeqDeserializer<'de> {
    iter: std::vec::IntoIter<Value>,
    phantom: std::marker::PhantomData<&'de ()>,
}

impl<'de> SeqDeserializer<'de> {
    fn new(list: Vec<Value>) -> Self {
        SeqDeserializer {
            iter: list.into_iter(),
            phantom: std::marker::PhantomData,
        }
    }
}

impl<'de> de::SeqAccess<'de> for SeqDeserializer<'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: de::DeserializeSeed<'de>,
    {
        let value = self.iter.next();

        match value {
            Some(value) => seed.deserialize(Deserializer::new(value)).map(Some),
            None => Ok(None),
        }
    }
}
