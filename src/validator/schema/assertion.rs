// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::utils::TryValue;
use super::SchemaError::{self, UnexpectedValue};
use super::{subschema::Subschema, ValidationError};
use regex::Regex;
use serde_json::{json, Number, Value};
use std::{cmp::Ordering, collections::HashSet};

/// A type that can be used in [SchemaAssertion::Type] or
/// [SchemaAssertion::Enum]
#[derive(Debug, PartialEq)]
pub enum InstanceType {
    /// A [Value::Null].
    Null,
    /// A [Value::Bool].
    Boolean,
    /// A [Value::Object].
    Object,
    /// A [Value::Array].
    Array,
    /// A [Value::Number].
    Number,
    /// A [Value::Number] that represents an integer.
    Integer,
    /// A [Value::String].
    String,
}

impl<'a> TryFrom<&'a str> for InstanceType {
    type Error = SchemaError<'a>;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match s {
            "null" => Ok(InstanceType::Null),
            "boolean" => Ok(InstanceType::Boolean),
            "object" => Ok(InstanceType::Object),
            "array" => Ok(InstanceType::Array),
            "number" => Ok(InstanceType::Number),
            "integer" => Ok(InstanceType::Integer),
            "string" => Ok(InstanceType::String),
            _ => Err(SchemaError::UnkownInstanceType(s)),
        }
    }
}
impl<'a> TryFrom<&'a String> for InstanceType {
    type Error = SchemaError<'a>;

    fn try_from(s: &'a String) -> Result<Self, Self::Error> {
        Self::try_from(s as &str)
    }
}

impl PartialEq<Value> for InstanceType {
    fn eq(&self, other: &Value) -> bool {
        match self {
            InstanceType::Null => other.is_null(),
            InstanceType::Boolean => other.is_boolean(),
            InstanceType::Object => other.is_object(),
            InstanceType::Array => other.is_array(),
            InstanceType::Number => other.is_number(),
            InstanceType::Integer => {
                other.as_number().map_or(false, |n| n.as_f64().map_or(true, |n| n.fract() == 0.0))
            }
            InstanceType::String => other.is_string(),
        }
    }
}

/// An assertion
#[derive(Debug)]
pub enum SchemaAssertion<'a> {
    /// Succeeds if the type of the instance matches at least one of the given
    /// types.
    Type(Vec<InstanceType>),
    /// Succeeds if the instance is equal to one of the elements in this
    /// keyword’s array value.
    Enum(&'a Vec<Value>),
    /// Succeeds if the instance is equal to this keyword’s value.
    Const(&'a Value),
    /// Succeeds if the regular expression matches the instance.
    Pattern(Regex),
    /// Succeeds if the numeric instance is greater than or equal to the given
    /// number.
    Minimum(&'a Number),
    /// Succeeds if the numeric instance is greater than the given number.
    ExclusiveMinimum(&'a Number),
    /// Succeeds if the numeric instance is less than or equal to the given
    /// number.
    Maximum(&'a Number),
    /// Succeeds if the numeric instance is less than the given number.
    ExclusiveMaximum(&'a Number),
    /// Succeeds if the instance array's size is less than, or equal to, the
    /// value of this keyword.
    MaxItems(&'a Number),
    /// Succeeds if the instance array's size is greater than, or equal to, the
    /// value of this keyword.
    MinItems(&'a Number),
    /// If `true`, the array instance validates successfully if all of its
    /// elements are unique.
    UniqueItems(bool),
    /// Succeeds if all of the listed properties are present on the instance
    /// object.
    Required(HashSet<&'a str>),
    //
    // Unimplemented ones
    //
    // DependentRequired,
    // minProperties,
    // maxProperties,
    // MultipleOf(Number),
    // MaxLength(u32),
    // MinLength(u32),
    // MinContains,
    // MaxContains,
}

impl<'a> SchemaAssertion<'a> {
    /// Creates an [SchemaAssertion::Type] from a json [Value]. The [Value]
    /// should be a string or an array of strings.
    pub fn try_new_type(value: &Value) -> Result<Self, SchemaError> {
        Ok(SchemaAssertion::Type(match value {
            Value::String(str) => vec![str.try_into()?],
            Value::Array(arr) => {
                arr.iter().map(|s| s.try_str()?.try_into()).collect::<Result<Vec<_>, _>>()?
            }
            _ => return Err(UnexpectedValue { expected: "string or array", value }),
        }))
    }

    /// Creates an [SchemaAssertion::Enum] from a json [Value]. The [Value]
    /// should be a non-empty array (of any type).
    pub fn try_new_enum(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        let arr = v.try_array()?;
        if arr.len() > 0 {
            Ok(SchemaAssertion::Enum(arr))
        } else {
            Err(SchemaError::UnexpectedValue { expected: "non-empty array", value: v })
        }
    }

    /// Creates an [SchemaAssertion::Const] from a json [Value].
    pub fn new_const(v: &'a Value) -> Self {
        SchemaAssertion::Const(v)
    }

    /// Creates an [SchemaAssertion::Pattern] from a json [Value]. The [Value]
    /// should be a valid regular expression string.
    pub fn try_new_pattern(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::Pattern(Regex::new(v.try_str()?).map_err(SchemaError::RegexError)?))
    }

    /// Creates an [SchemaAssertion::Minimum] from a json [Value]. The [Value]
    /// should be a number.
    pub fn try_new_min(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::Minimum(v.try_number()?))
    }

    /// Creates an [SchemaAssertion::ExclusiveMinimum] from a json [Value]. The
    /// [Value] should be a number.
    pub fn try_new_xmin(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::ExclusiveMinimum(v.try_number()?))
    }

    /// Creates an [SchemaAssertion::Maximum] from a json [Value]. The [Value]
    /// should be a number.
    pub fn try_new_max(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::Maximum(v.try_number()?))
    }

    /// Creates an [SchemaAssertion::ExclusiveMaximum] from a json [Value]. The
    /// [Value] should be a number.
    pub fn try_new_xmax(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::ExclusiveMaximum(v.try_number()?))
    }

    /// Creates an [SchemaAssertion::MinItems] from a json [Value]. The [Value]
    /// should be a number.
    pub fn try_new_min_items(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::MinItems(v.try_number()?))
    }

    /// Creates an [SchemaAssertion::MaxItems] from a json [Value]. The [Value]
    /// should be a number.
    pub fn try_new_max_items(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::MaxItems(v.try_number()?))
    }

    /// Creates an [SchemaAssertion::UniqueItems] from a json [Value]. The
    /// [Value] should be a boolean.
    pub fn try_new_unique_items(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::UniqueItems(v.try_bool()?))
    }

    /// Creates an [SchemaAssertion::Required] from a json [Value]. The [Value]
    /// should be an array of unique strings.
    pub fn try_new_required(v: &'a Value) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaAssertion::Required(
            v.try_array()?.iter().map(|v| v.try_str()).collect::<Result<HashSet<_>, _>>()?,
        ))
    }

    pub fn validate<'i>(
        &self,
        instance: &'i Value,
        subschema: &'a Subschema<'a>,
    ) -> Result<(), ValidationError<'i, 'a>> {
        if match self {
            SchemaAssertion::Type(vec) => vec.iter().any(|t| t == instance),
            SchemaAssertion::Enum(vec) => vec.contains(instance),
            SchemaAssertion::Const(value) => *value == instance,
            SchemaAssertion::Pattern(re) => instance.as_str().map_or(true, |s| re.is_match(s)),
            SchemaAssertion::Minimum(limit) => {
                instance.as_number().map_or(true, |n| compare(n, limit).is_ge())
            }
            SchemaAssertion::ExclusiveMinimum(limit) => {
                instance.as_number().map_or(true, |n| compare(n, limit).is_gt())
            }
            SchemaAssertion::Maximum(limit) => {
                instance.as_number().map_or(true, |n| compare(n, limit).is_le())
            }
            SchemaAssertion::ExclusiveMaximum(limit) => {
                instance.as_number().map_or(true, |n| compare(n, limit).is_lt())
            }
            SchemaAssertion::MaxItems(limit) => {
                instance.as_array().map_or(true, |a| compare(&Number::from(a.len()), limit).is_le())
            }
            SchemaAssertion::MinItems(limit) => {
                instance.as_array().map_or(true, |a| compare(&Number::from(a.len()), limit).is_ge())
            }
            SchemaAssertion::UniqueItems(unique) => {
                let mut seen = HashSet::new();
                instance.as_array().map_or(true, |a| !unique || a.iter().all(|v| seen.insert(v)))
            }
            SchemaAssertion::Required(req) => {
                instance.as_object().map_or(true, |o| req.iter().all(|p| o.contains_key(*p)))
            }
        } {
            Ok(())
        } else {
            Err(ValidationError { instance, subschema })
        }
    }
}

fn compare(left: &Number, right: &Number) -> Ordering {
    // TODO: b/381985258 - Correctly compare
    left.as_f64().unwrap().partial_cmp(&right.as_f64().unwrap()).unwrap()
}

#[cfg(test)]
mod test {
    use super::*;
    use Subschema::Bool;

    #[test]
    fn test_instance_type_parse() {
        assert_eq!(InstanceType::try_from("null").unwrap(), InstanceType::Null);
        assert_eq!(InstanceType::try_from("boolean").unwrap(), InstanceType::Boolean);
        assert_eq!(InstanceType::try_from("object").unwrap(), InstanceType::Object);
        assert_eq!(InstanceType::try_from("array").unwrap(), InstanceType::Array);
        assert_eq!(InstanceType::try_from("number").unwrap(), InstanceType::Number);
        assert_eq!(InstanceType::try_from("integer").unwrap(), InstanceType::Integer);
        assert_eq!(InstanceType::try_from("string").unwrap(), InstanceType::String);
        assert!(InstanceType::try_from("somethingElse").is_err());
    }

    #[test]
    fn test_instance_type_value_partial_equality() {
        assert_eq!(InstanceType::Null, json!(null));
        assert_eq!(InstanceType::Boolean, json!(true));
        assert_eq!(InstanceType::Object, json!({"key":42}));
        assert_eq!(InstanceType::Array, json!([42]));
        assert_eq!(InstanceType::Number, json!(42));
        assert_eq!(InstanceType::Number, json!(42.42));
        assert_eq!(InstanceType::Integer, json!(42));
        assert_ne!(InstanceType::Integer, json!(42.42));
        assert_eq!(InstanceType::String, json!("str"));
    }

    #[test]
    fn test_new_type() {
        assert!(matches!(
            SchemaAssertion::try_new_type(&json!("integer")),
            Ok(SchemaAssertion::Type(v)) if v == &[InstanceType::Integer]
        ));
        assert!(matches!(SchemaAssertion::try_new_type(&json!(42)), Err(_)));
        assert!(matches!(
            SchemaAssertion::try_new_type(&json!(["integer", "string"])),
            Ok(SchemaAssertion::Type(v)) if v == &[InstanceType::Integer, InstanceType::String]
        ));
        assert!(matches!(SchemaAssertion::try_new_type(&json!([[], "string"])), Err(_)));
    }

    #[test]
    fn test_new_enum() {
        assert!(matches!(
            SchemaAssertion::try_new_enum(&json!([1, 2.1, true, "3", [], null, {"foo": 42}])),
            Ok(SchemaAssertion::Enum(v)) if v == &[json!(1), json!(2.1), json!(true),json!("3"), json!([]), json!(null), json!({"foo":42}),]
        ));

        assert!(matches!(SchemaAssertion::try_new_enum(&json!(42)), Err(_)));
        assert!(matches!(SchemaAssertion::try_new_enum(&json!([])), Err(_)));
    }

    #[test]
    fn test_new_const() {
        let value = &json!({"foo": 42, "bar": [null, 2]});
        assert!(
            matches!(&SchemaAssertion::new_const(value), SchemaAssertion::Const(&ref v) if v == value)
        );
    }

    #[test]
    fn test_new_pattern() {
        let re = Regex::new("(foo|bar|baz)").unwrap();
        assert!(matches!(
            &SchemaAssertion::try_new_pattern(&json!(re.as_str())),
            Ok(SchemaAssertion::Pattern(r)) if r.as_str() == re.as_str()));

        assert!(matches!(SchemaAssertion::try_new_pattern(&json!("(foo|bar")), Err(_)));
        assert!(matches!(SchemaAssertion::try_new_pattern(&json!([re.as_str()])), Err(_)));
    }

    #[test]
    fn test_new_min() {
        let num = &Number::from_f64(42.1).unwrap();

        assert!(matches!(
            &SchemaAssertion::try_new_min(&json!(num)),
            Ok(SchemaAssertion::Minimum(&ref n)) if n == num));

        assert!(matches!(SchemaAssertion::try_new_min(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_xmin() {
        let num = &Number::from_f64(42.1).unwrap();

        assert!(matches!(
            &SchemaAssertion::try_new_xmin(&json!(num)),
            Ok(SchemaAssertion::ExclusiveMinimum(&ref n)) if n == num
        ));

        assert!(matches!(SchemaAssertion::try_new_xmin(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_max() {
        let num = &Number::from_f64(42.1).unwrap();

        assert!(matches!(
            &SchemaAssertion::try_new_max(&json!(num)),
            Ok(SchemaAssertion::Maximum(&ref n)) if n == num
        ));

        assert!(matches!(SchemaAssertion::try_new_max(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_xmax() {
        let num = &Number::from_f64(42.1).unwrap();

        assert!(matches!(
            &SchemaAssertion::try_new_xmax(&json!(num)),
            Ok(SchemaAssertion::ExclusiveMaximum(&ref n)) if n == num
        ));

        assert!(matches!(SchemaAssertion::try_new_xmax(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_min_items() {
        let num = &Number::from_f64(42.1).unwrap();

        assert!(matches!(
            &SchemaAssertion::try_new_min_items(&json!(num)),
            Ok(SchemaAssertion::MinItems(&ref n)) if n == num
        ));

        assert!(matches!(SchemaAssertion::try_new_min_items(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_max_items() {
        let num = &Number::from_f64(42.1).unwrap();

        assert!(matches!(
            &SchemaAssertion::try_new_max_items(&json!(num)),
            Ok(SchemaAssertion::MaxItems(&ref n)) if n == num
        ));

        assert!(matches!(SchemaAssertion::try_new_max_items(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_unique_items() {
        assert!(matches!(
            &SchemaAssertion::try_new_unique_items(&json!(true)),
            Ok(SchemaAssertion::UniqueItems(true))
        ));

        assert!(matches!(SchemaAssertion::try_new_unique_items(&json!("foo")), Err(_)));
    }

    #[test]
    fn test_new_required() {
        assert!(matches!(
            SchemaAssertion::try_new_required(&json!(["foo", "bar"])),
            Ok(SchemaAssertion::Required(v)) if v == HashSet::from(["foo", "bar"])
        ));

        assert!(matches!(SchemaAssertion::try_new_required(&json!(42)), Err(_)));
        assert!(matches!(SchemaAssertion::try_new_required(&json!(["foo", 42])), Err(_)));
    }

    //  ┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
    //  ┃               Validation tests                  ┃
    //  ┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛

    #[test]
    fn test_validate_type() {
        assert!(SchemaAssertion::Type(vec![InstanceType::String])
            .validate(&json!("42"), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Type(vec![InstanceType::String, InstanceType::Number])
            .validate(&json!(42), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Type(vec![InstanceType::Integer])
            .validate(&json!(42.0), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::Type(vec![InstanceType::String, InstanceType::Null])
            .validate(&json!(42), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_enum() {
        let e = vec![json!(42), json!(null), json!("foo")];
        assert!(SchemaAssertion::Enum(&e).validate(&json!(42), &Bool(true)).is_ok());
        assert!(SchemaAssertion::Enum(&e).validate(&json!(null), &Bool(true)).is_ok());
        assert!(SchemaAssertion::Enum(&e).validate(&json!("foo"), &Bool(true)).is_ok());

        assert!(SchemaAssertion::Enum(&e)
            .validate(&json!([42, null, "foo"]), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_const() {
        assert!(SchemaAssertion::Const(&json!(42.123))
            .validate(&json!(42.123), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Const(&json!({"foo": 42}))
            .validate(&json!({"foo":42}), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Const(&json!(null)).validate(&json!(null), &Bool(true)).is_ok());

        assert!(SchemaAssertion::Const(&json!(42)).validate(&json!("42"), &Bool(true)).is_err());
        assert!(SchemaAssertion::Const(&json!(null)).validate(&json!([]), &Bool(true)).is_err());
    }

    #[test]
    fn test_validate_pattern() {
        assert!(SchemaAssertion::Pattern(Regex::new("(foo|bar)").unwrap())
            .validate(&json!("foo"), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Pattern(Regex::new("(foo|bar)").unwrap())
            .validate(&json!(42), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Pattern(Regex::new("^(foo|bar)$").unwrap())
            .validate(&json!(["foot"]), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::Pattern(Regex::new("^(foo|bar)$").unwrap())
            .validate(&json!("foot"), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_min() {
        assert!(SchemaAssertion::Minimum(&Number::from_i128(10).unwrap())
            .validate(&json!(10), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Minimum(&Number::from_i128(10).unwrap())
            .validate(&json!(11), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Minimum(&Number::from_i128(10).unwrap())
            .validate(&json!("0"), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Minimum(&Number::from_i128(10).unwrap())
            .validate(&json!(null), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Minimum(&Number::from_f64(3.14).unwrap())
            .validate(&json!(3.14), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::Minimum(&Number::from_i128(10).unwrap())
            .validate(&json!(9), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_xmin() {
        assert!(SchemaAssertion::ExclusiveMinimum(&Number::from_i128(10).unwrap())
            .validate(&json!(11), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::ExclusiveMinimum(&Number::from_i128(10).unwrap())
            .validate(&json!("0"), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::ExclusiveMinimum(&Number::from_i128(10).unwrap())
            .validate(&json!(null), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::ExclusiveMinimum(&Number::from_i128(10).unwrap())
            .validate(&json!(10), &Bool(true))
            .is_err());
        assert!(SchemaAssertion::ExclusiveMinimum(&Number::from_f64(3.14).unwrap())
            .validate(&json!(3.14), &Bool(true))
            .is_err());
        assert!(SchemaAssertion::ExclusiveMinimum(&Number::from_i128(10).unwrap())
            .validate(&json!(9), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_max() {
        assert!(SchemaAssertion::Maximum(&Number::from_i128(10).unwrap())
            .validate(&json!(10), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Maximum(&Number::from_i128(10).unwrap())
            .validate(&json!(9), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Maximum(&Number::from_i128(10).unwrap())
            .validate(&json!(-11), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Maximum(&Number::from_i128(10).unwrap())
            .validate(&json!("0"), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Maximum(&Number::from_i128(10).unwrap())
            .validate(&json!(null), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::Maximum(&Number::from_f64(3.14).unwrap())
            .validate(&json!(3.14), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::Maximum(&Number::from_i128(10).unwrap())
            .validate(&json!(11), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_xmax() {
        assert!(SchemaAssertion::ExclusiveMaximum(&Number::from_i128(10).unwrap())
            .validate(&json!(9), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::ExclusiveMaximum(&Number::from_i128(10).unwrap())
            .validate(&json!("0"), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::ExclusiveMaximum(&Number::from_i128(10).unwrap())
            .validate(&json!(null), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::ExclusiveMaximum(&Number::from_i128(10).unwrap())
            .validate(&json!(10), &Bool(true))
            .is_err());
        assert!(SchemaAssertion::ExclusiveMaximum(&Number::from_f64(3.14).unwrap())
            .validate(&json!(3.14), &Bool(true))
            .is_err());
        assert!(SchemaAssertion::ExclusiveMaximum(&Number::from_i128(10).unwrap())
            .validate(&json!(11), &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_min_items() {
        let arr = &json!([1, 2, "3", null, []]);
        assert!(SchemaAssertion::MinItems(&Number::from_i128(4).unwrap())
            .validate(arr, &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::MinItems(&Number::from_i128(5).unwrap())
            .validate(arr, &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::MinItems(&Number::from_i128(5).unwrap())
            .validate(&json!(42), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::MinItems(&Number::from_i128(6).unwrap())
            .validate(arr, &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_max_items() {
        let arr = &json!([1, 2, "3", null, []]);
        assert!(SchemaAssertion::MaxItems(&Number::from_i128(6).unwrap())
            .validate(arr, &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::MaxItems(&Number::from_i128(5).unwrap())
            .validate(arr, &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::MaxItems(&Number::from_i128(5).unwrap())
            .validate(&json!(42), &Bool(true))
            .is_ok());

        assert!(SchemaAssertion::MaxItems(&Number::from_i128(4).unwrap())
            .validate(arr, &Bool(true))
            .is_err());
    }

    #[test]
    fn test_validate_unique_items() {
        assert!(SchemaAssertion::UniqueItems(true)
            .validate(&json!([1, 2, null, false]), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::UniqueItems(true).validate(&json!([]), &Bool(true)).is_ok());
        assert!(SchemaAssertion::UniqueItems(true).validate(&json!(42), &Bool(true)).is_ok());
        assert!(SchemaAssertion::UniqueItems(false)
            .validate(&json!([1, 2, null, false]), &Bool(true))
            .is_ok());
        assert!(SchemaAssertion::UniqueItems(false).validate(&json!([2, 2]), &Bool(true)).is_ok());

        assert!(SchemaAssertion::UniqueItems(true).validate(&json!([2, 2]), &Bool(true)).is_err());
    }

    #[test]
    fn test_validate_required() {
        let a = SchemaAssertion::Required(HashSet::from(["foo", "bar"]));
        assert!(a.validate(&json!({"foo": 42, "bar": null}), &Bool(true)).is_ok());
        assert!(a.validate(&json!({"foo": 42, "bar": null, "baz": false}), &Bool(true)).is_ok());
        assert!(a.validate(&json!(42), &Bool(true)).is_ok());

        assert!(a.validate(&json!({"foo": 42}), &Bool(true)).is_err());
    }
}
