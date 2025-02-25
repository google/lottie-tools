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

use super::pointer::RefResolver;
use super::utils::TryValue;
use super::{subschema::Subschema, SchemaError, SchemaKeyword, ValidationError};
use serde_json::Value;
use std::collections::{HashMap, HashSet};

/// An applicator
#[derive(Debug)]
pub enum SchemaApplicator<'a> {
    /// Succeeds if exactly one of the subschemas defined by this keyword’s
    /// value succeed.
    OneOf(Vec<Subschema<'a>>),
    /// Succeeds if at least one of the subschemas defined by this keyword’s
    /// value succeed.
    AnyOf(Vec<Subschema<'a>>),
    /// Succeeds if all of the subschemas defined by this keyword’s value
    /// succeed.
    AllOf(Vec<Subschema<'a>>),
    /// If the `if` subschema succeeds, the validation succeeds
    /// if the instance validates against the `then` subschema successfully
    /// too (or if the `then` subschema is unavailable). Otherwise (when
    /// `if` subschema validation fails) it'll succeed if the instance validates
    /// against the `else` subschema successfully (or if the `else` subschema is
    /// unavailable).
    IfThenElse(Subschema<'a>, Option<Subschema<'a>>, Option<Subschema<'a>>),
    /// Succeeds if the instance fails to validate against the subschema.
    Not(Subschema<'a>),
    /// Succeds if all of the properties in the instance validate against their
    /// corresponding subschema from this keyword (if they have one).
    Properties(HashMap<&'a str, Subschema<'a>>),
    /// Succeeds if the subschema validates against each value not matched by
    /// other object applicators.
    AdditionalProperties(Subschema<'a>),
    /// Succeeds if each item in the instance array that hasn't been matched by
    /// `prefixItems` validates against this subschema.
    Items(Subschema<'a>),
    /// Succeeds if the subschema validates against each value not matched by
    /// other object applicators (or their valid children).
    UnevaluatedProperties(Subschema<'a>),
    //
    // Unimplemented ones
    //
    // UnevaluatedItems,
    // PatternProperties,
    // PropertyNames,
    // DependentSchemas,
    // Contains,
    // PrefixItems
}

impl<'a, 'b> SchemaApplicator<'a> {
    /// Creates an [SchemaApplicator::OneOf] from a json [Value]. The
    /// [Value] should be a non-empty array of valid subschemas.
    pub fn try_new_one_of(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::OneOf(
            value
                .try_array()?
                .iter()
                .map(|v| Subschema::from_json(v, ref_resolver))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    /// Creates an [SchemaApplicator::AnyOf] from a json [Value]. The
    /// [Value] should be a non-empty array of valid subschemas.
    pub fn try_new_any_of(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::AnyOf(
            value
                .try_array()?
                .iter()
                .map(|v| Subschema::from_json(v, ref_resolver))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    /// Creates an [SchemaApplicator::AllOf] from a json [Value]. The
    /// [Value] should be a non-empty array of valid subschemas.
    pub fn try_new_all_of(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::AllOf(
            value
                .try_array()?
                .iter()
                .map(|v| Subschema::from_json(v, ref_resolver))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    /// Creates an [SchemaApplicator::IfThenElse] from if/then/else [Value]s
    /// from an object map. The three [Value]s (if present) should be
    /// valid subschemas.
    pub fn try_new_if_then_else(
        if_value: &'a Value,
        then_value: Option<&'a Value>,
        else_value: Option<&'a Value>,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::IfThenElse(
            Subschema::from_json(if_value, ref_resolver)?,
            then_value.map(|v| Subschema::from_json(v, ref_resolver)).transpose()?,
            else_value.map(|v| Subschema::from_json(v, ref_resolver)).transpose()?,
        ))
    }

    /// Creates an [SchemaApplicator::Not] from a json [Value]. The
    /// [Value] should be a valid subschema.
    pub fn try_new_not(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::Not(Subschema::from_json(value, ref_resolver)?))
    }

    /// Creates an [SchemaApplicator::Properties] from a json [Value]. The
    /// [Value] should be an object where each of its value is a json
    /// subschema.
    pub fn try_new_properties(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::Properties(
            value
                .try_object()?
                .iter()
                .map(|(k, v)| Subschema::from_json(v, ref_resolver).map(|s| (k.as_str(), s)))
                .collect::<Result<HashMap<_, _>, _>>()?,
        ))
    }

    /// Creates an [SchemaApplicator::AdditionalProperties] from a json [Value].
    /// The [Value] should be a valid subschema.
    pub fn try_additional_properties(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::AdditionalProperties(Subschema::from_json(value, ref_resolver)?))
    }

    /// Creates an [SchemaApplicator::Items] from a json [Value]. The
    /// [Value] should be a valid subschema.
    pub fn try_new_items(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::Items(Subschema::from_json(value, ref_resolver)?))
    }

    /// Creates an [SchemaApplicator::UnEvaluatedProperties] from a json
    /// [Value]. The [Value] should be a valid subschema.
    pub fn try_unevaluated_properties(
        value: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        Ok(SchemaApplicator::UnevaluatedProperties(Subschema::from_json(value, ref_resolver)?))
    }

    pub fn validate<'i>(
        &'a self,
        instance: &'i Value,
        subschema: &'a Subschema<'a>,
        validated_props: &mut HashSet<&'i str>,
        evaluated_props: &mut HashSet<&'i str>,
    ) -> Result<(), ValidationError<'i, 'a>> {
        let mut sub_evaluated_props = HashSet::new();
        if match self {
            // TODO: b/381985258 - Report a more granular failure
            SchemaApplicator::OneOf(vec) => {
                vec.iter()
                    .filter(|s| s.continue_validation(instance, &mut sub_evaluated_props).is_ok())
                    .count()
                    == 1
            }
            // TODO: b/381985258 - Report a more granular failure
            SchemaApplicator::AnyOf(vec) => {
                // Using fold instead of any to avoid short circuiting which can leave the
                // sub_evaluated_props incomplete.
                vec.iter().fold(false, |result, s| {
                    s.continue_validation(instance, &mut sub_evaluated_props).is_ok() || result
                })
            }
            // TODO: b/381985258 - Report a more granular failure
            SchemaApplicator::AllOf(vec) => vec
                .iter()
                .all(|s| s.continue_validation(instance, &mut sub_evaluated_props).is_ok()),
            SchemaApplicator::IfThenElse(if_s, then_s, else_s) => {
                if if_s.continue_validation(instance, &mut sub_evaluated_props).is_ok() {
                    then_s.as_ref().map_or(Ok(()), |then_s| {
                        then_s.continue_validation(instance, &mut sub_evaluated_props)
                    })?
                } else {
                    else_s.as_ref().map_or(Ok(()), |else_s| {
                        else_s.continue_validation(instance, &mut sub_evaluated_props)
                    })?
                }
                true
            }
            // TODO: b/381985258 - Report a more granular failure
            SchemaApplicator::Not(s) => {
                s.continue_validation(instance, &mut sub_evaluated_props).is_err()
            }
            SchemaApplicator::Properties(props) => instance.as_object().map_or(Ok(true), |m| {
                for (prop_name, prop_schema) in props {
                    if let Some((prop_key, prop_instance)) = m.get_key_value(*prop_name) {
                        prop_schema.validate(prop_instance)?;
                        validated_props.insert(prop_key);
                        sub_evaluated_props.insert(prop_key);
                    }
                }
                Ok(true)
            })?,
            SchemaApplicator::AdditionalProperties(s) => {
                instance.as_object().map_or(Ok(true), |m| {
                    for (prop_name, prop_value) in m {
                        if validated_props.contains(prop_name.as_str()) {
                            continue;
                        }
                        s.validate(prop_value)?;
                        sub_evaluated_props.insert(prop_name);
                    }
                    Ok(true)
                })?
            }
            // TODO: b/381985258 - Report a more granular failure
            SchemaApplicator::Items(s) => {
                instance.as_array().map_or(true, |a| a.iter().all(|v| s.validate(v).is_ok()))
            }
            SchemaApplicator::UnevaluatedProperties(s) => {
                // This keyword is always put last on the list, so we can assume that other
                // applicators have already contributed to `evaluated_props`
                instance.as_object().map_or(Ok(true), |m| {
                    for (prop_name, prop_value) in m {
                        if evaluated_props.contains(prop_name.as_str()) {
                            continue;
                        }
                        s.validate(prop_value)?;
                        sub_evaluated_props.insert(prop_name);
                    }
                    Ok(true)
                })?
            }
        } {
            evaluated_props.extend(sub_evaluated_props);
            Ok(())
        } else {
            Err(ValidationError { instance, subschema })
        }
    }
}

#[cfg(test)]
mod test {
    // TOOD: b/381985258 - Add comments explaining what each test is doing.
    use super::*;
    use crate::validator::schema::assertion::{InstanceType, SchemaAssertion};
    use serde_json::{json, Number};
    use InstanceType::{Boolean, Integer};
    use SchemaAssertion::{Minimum, Type};
    use SchemaKeyword::Assertion;
    use Subschema::{Bool, Object};

    macro_rules! validates {
        ($schema:expr, $instance:expr) => {
            $schema
                .validate($instance, &Bool(true), &mut HashSet::new(), &mut HashSet::new())
                .is_ok()
        };
    }

    //  ┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
    //  ┃               Validation tests                  ┃
    //  ┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛

    #[test]
    fn test_validate_one_of() {
        let min_number = Number::from_i128(0).unwrap();

        assert!(validates!(
            SchemaApplicator::OneOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))])
            ]),
            &json!(42)
        ));

        assert!(!validates!(
            SchemaApplicator::OneOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))])
            ]),
            &json!("42")
        ));
        assert!(!validates!(
            SchemaApplicator::OneOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))]),
                Object(vec![Assertion(Minimum(&min_number))])
            ]),
            &json!(42)
        ));
    }

    #[test]
    fn test_validate_any_of() {
        let min_number = Number::from_i128(0).unwrap();

        assert!(validates!(
            SchemaApplicator::AnyOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))])
            ]),
            &json!(42)
        ));
        assert!(validates!(
            SchemaApplicator::AnyOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))]),
                Object(vec![Assertion(Minimum(&min_number))])
            ]),
            &json!(42)
        ));

        assert!(!validates!(
            SchemaApplicator::AnyOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))])
            ]),
            &json!("42")
        ));
    }

    #[test]
    fn test_validate_all_of() {
        let min_number = Number::from_i128(0).unwrap();

        assert!(validates!(
            SchemaApplicator::AllOf(vec![Bool(true), Object(vec![Assertion(Type(vec![Integer]))])]),
            &json!(42)
        ));
        assert!(validates!(
            SchemaApplicator::AllOf(vec![
                Object(vec![Assertion(Type(vec![Integer]))]),
                Object(vec![Assertion(Minimum(&min_number))])
            ]),
            &json!(42)
        ));

        assert!(!validates!(
            SchemaApplicator::AllOf(vec![
                Bool(false),
                Object(vec![Assertion(Type(vec![Integer]))])
            ]),
            &json!("42")
        ));
    }

    #[test]
    fn test_validate_if_then_else() {
        // Valid "if" & valid "then" -> Valid
        assert!(validates!(
            SchemaApplicator::IfThenElse(
                Bool(true),
                Some(Object(vec![Assertion(Type(vec![Integer]))])),
                Some(Bool(false))
            ),
            &json!(42)
        ));

        // Invalid "if" & valid "else" -> Valid
        assert!(validates!(
            SchemaApplicator::IfThenElse(
                Bool(false),
                Some(Bool(false)),
                Some(Object(vec![Assertion(Type(vec![Integer]))])),
            ),
            &json!(42)
        ));

        // Valid "if" & missing "then" -> Valid
        assert!(validates!(
            SchemaApplicator::IfThenElse(Bool(true), None, Some(Bool(false))),
            &json!(42)
        ));

        // Invalid "if" & missing "else" -> Valid
        assert!(validates!(
            SchemaApplicator::IfThenElse(Bool(false), Some(Bool(false)), None),
            &json!(42)
        ));

        // Valid "if" & invalid "then" -> Invalid
        assert!(!validates!(
            SchemaApplicator::IfThenElse(
                Bool(true),
                Some(Object(vec![Assertion(Type(vec![Integer]))])),
                None
            ),
            &json!("42")
        ));

        // Invalid "if" & invalid "else" -> Invalid
        assert!(!validates!(
            SchemaApplicator::IfThenElse(
                Bool(false),
                None,
                Some(Object(vec![Assertion(Type(vec![Integer]))]))
            ),
            &json!("42")
        ));
    }

    #[test]
    fn test_validate_not() {
        assert!(validates!(
            SchemaApplicator::Not(Object(vec![Assertion(Type(vec![Integer]))])),
            &json!("42")
        ));
        assert!(validates!(SchemaApplicator::Not(Bool(false)), &json!(42)));

        assert!(!validates!(
            SchemaApplicator::Not(Object(vec![Assertion(Type(vec![Integer]))])),
            &json!(42)
        ));
    }

    #[test]
    fn test_validate_items() {
        assert!(validates!(
            SchemaApplicator::Items(Object(vec![Assertion(Type(vec![Integer]))])),
            &json!([42, 43])
        ));
        assert!(validates!(
            SchemaApplicator::Items(Object(vec![Assertion(Type(vec![Integer]))])),
            &json!("42")
        ));

        assert!(!validates!(
            SchemaApplicator::Items(Object(vec![Assertion(Type(vec![Integer]))])),
            &json!(["42", 43])
        ));
    }

    #[test]
    fn test_validate_properties() {
        let object_map = HashMap::from([
            ("foo", Object(vec![Assertion(Type(vec![Integer]))])),
            ("bar", Bool(false)),
        ]);
        let applicator = SchemaApplicator::Properties(object_map);

        let value = json!({"foo": 42});
        let mut validated_props = HashSet::new();
        let mut evaluated_props = HashSet::new();
        assert!(applicator
            .validate(&value, &Bool(true), &mut validated_props, &mut evaluated_props)
            .is_ok());
        assert_eq!(validated_props, HashSet::from(["foo"]));
        assert_eq!(evaluated_props, HashSet::from(["foo"]));

        let value = json!({"foo": 42, "baz": false});
        let mut validated_props = HashSet::new();
        let mut evaluated_props = HashSet::new();
        assert!(applicator
            .validate(&value, &Bool(true), &mut validated_props, &mut evaluated_props)
            .is_ok());
        assert_eq!(validated_props, HashSet::from(["foo"]));
        assert_eq!(evaluated_props, HashSet::from(["foo"]));

        let value = json!({"foo": 42, "bar":42});
        let mut validated_props = HashSet::new();
        let mut evaluated_props = HashSet::new();
        assert!(applicator
            .validate(&value, &Bool(true), &mut validated_props, &mut evaluated_props)
            .is_err());
        assert!(evaluated_props.is_empty());
    }

    #[test]
    fn test_validate_additional_properties() {
        let applicator =
            SchemaApplicator::AdditionalProperties(Object(vec![Assertion(Type(vec![Boolean]))]));

        let inst = json!({"foo": 42});
        let mut evaluated_props = HashSet::new();
        assert!(applicator
            .validate(&inst, &Bool(true), &mut HashSet::from(["foo"]), &mut evaluated_props)
            .is_ok());
        assert!(evaluated_props.is_empty());

        let inst = json!({"foo": 42, "bar":false});
        let mut evaluated_props = HashSet::from(["foo"]);
        assert!(applicator
            .validate(&inst, &Bool(true), &mut HashSet::from(["foo"]), &mut evaluated_props)
            .is_ok());
        assert_eq!(evaluated_props, HashSet::from(["foo", "bar"]));

        let inst = json!({"foo": 42, "bar":42});
        let mut evaluated_props = HashSet::from(["foo"]);
        assert!(applicator
            .validate(&inst, &Bool(true), &mut HashSet::from(["foo"]), &mut evaluated_props)
            .is_err());
        assert_eq!(evaluated_props, HashSet::from(["foo"]));
    }

    #[test]
    fn test_validate_unevaluated_properties() {
        let applicator =
            SchemaApplicator::UnevaluatedProperties(Object(vec![Assertion(Type(vec![Boolean]))]));

        assert!(applicator
            .validate(
                &json!({"foo": 42}),
                &Bool(true),
                &mut HashSet::from(["foo"]),
                &mut HashSet::from(["foo"])
            )
            .is_ok());
        assert!(applicator
            .validate(
                &json!({"foo": 42, "bar":false}),
                &Bool(true),
                &mut HashSet::from(["foo"]),
                &mut HashSet::from(["foo"])
            )
            .is_ok());

        assert!(applicator
            .validate(
                &json!({"foo": 42, "bar":42}),
                &Bool(true),
                &mut HashSet::from(["foo"]),
                &mut HashSet::from(["foo"])
            )
            .is_err());
    }
}
