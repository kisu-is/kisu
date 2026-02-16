use std::collections::HashMap;
use std::rc::Rc;

use miette::Diagnostic;
use serde::de::{self, DeserializeOwned, IntoDeserializer, Visitor};

use crate::{eval::Value, run};

pub fn from_str<T>(source: &str) -> Result<T, miette::Error>
where
    T: DeserializeOwned,
{
    let value = run(source)?;
    let deserializer = Deserializer::new(value);
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
            Value::String(s) => visitor.visit_string(s.to_string()),
            Value::Struct(_name, map) => {
                let map_deserializer = MapDeserializer::new(map);
                visitor.visit_map(map_deserializer)
            }
            Value::List(l) => {
                let seq_deserializer = SeqDeserializer::new(l);
                visitor.visit_seq(seq_deserializer)
            }
            Value::Bool(b) => visitor.visit_bool(b),
            Value::Unit => visitor.visit_unit(),
            _ => Err(de::Error::custom(format!(
                "unsupported Value type for deserialization: {:?}",
                self.value
            ))),
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

    serde::forward_to_deserialize_any! {
        bool u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 char str string seq
        bytes byte_buf map unit
        ignored_any unit_struct tuple_struct tuple identifier
    }
}

struct MapDeserializer<'de> {
    iter: std::collections::hash_map::IntoIter<String, Value>,
    next_value: Option<Value>,
    phantom: std::marker::PhantomData<&'de ()>,
}

impl<'de> MapDeserializer<'de> {
    fn new(map: Rc<HashMap<String, Value>>) -> Self {
        let map_owned = match Rc::try_unwrap(map) {
            Ok(m) => m,
            Err(rc_map) => (*rc_map).clone(),
        };

        MapDeserializer {
            iter: map_owned.into_iter(),
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
            self.next_value = Some(value.clone());
            seed.deserialize(key.clone().into_deserializer()).map(Some)
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
    fn new(list: Rc<Vec<Value>>) -> Self {
        let list_owned = match Rc::try_unwrap(list) {
            Ok(l) => l,
            Err(rc_list) => (*rc_list).clone(),
        };

        SeqDeserializer {
            iter: list_owned.into_iter(),
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
            Some(value) => seed.deserialize(Deserializer::new(value.clone())).map(Some),
            None => Ok(None),
        }
    }
}
