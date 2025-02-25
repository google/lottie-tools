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

use core::fmt;
use serde_json::{json, Map, Value};
use std::cell::OnceCell;
use std::collections::HashSet;
use std::rc::Rc;
use std::vec;

use super::assertion::SchemaAssertion;
use super::pointer::RefResolver;
use super::utils::TryValue;
use super::SchemaError;
use super::{applicator::SchemaApplicator, ValidationError};

/// These keywords are ignored as they don't have an effect on the validation,
/// or (in case of `$defs`) they are indirectly used by other subschemas anyway.
const INGORED_KEYWORDS: &[&str] = &[
    "title",
    "description",
    "default",
    "$comment",
    "$defs",
    "$version",
    "examples",
    "$id",
    "$schema",
    // TODO: b/381985258 - Add these as metadata to Subschema
    "feature-code",
    "feature-level",
    "feature-details",
    "feature-link",
];

/// One of [SchemaAssertion], [SchemaApplicator] or [Ref].
pub enum SchemaKeyword<'a> {
    /// A reference to another subschema.
    Ref(Rc<OnceCell<Subschema<'a>>>),
    Assertion(SchemaAssertion<'a>),
    Applicator(SchemaApplicator<'a>),
}

impl fmt::Debug for SchemaKeyword<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            // TODO: b/381985258 - Include some identifier from the ref.
            // Due to potential loops in Ref, We can't Derive the Debug trait.
            SchemaKeyword::Ref(_) => f.write_str("$ref"),
            SchemaKeyword::Assertion(schema_assertion) => schema_assertion.fmt(f),
            SchemaKeyword::Applicator(schema_applicator) => schema_applicator.fmt(f),
        }
    }
}

/// Represents a subchema. Either a boolean or an object cotaining a list of
/// keywords to validate against.
#[derive(Debug)]
pub enum Subschema<'a> {
    /// An object subschema. The validation result of this subschema will be
    /// successful for an instance if **all** of the [SchemaKeyword]s in this
    /// subschema validate the given instance successfully.
    Object(Vec<SchemaKeyword<'a>>),
    /// A boolean subschema. Regardless of the instance content, the validation
    /// result is set by the boolean value of this subschema.
    Bool(bool),
}

impl<'a, 'b> Subschema<'a>
where
    'a: 'b,
{
    /// Creates a [Subschema] from a json [Value].
    pub fn from_json(
        input: &'a Value,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        match input {
            Value::Bool(b) => Ok(Subschema::Bool(*b)),
            Value::Object(map) => Ok(Self::from_object(map, ref_resolver)?),
            _ => Err(SchemaError::UnexpectedValue { expected: "object or boolean", value: input }),
        }
    }

    /// Validates a JSON instance against this subschema. This can be used at
    /// the rool level or when going the instance location changes due to
    /// walking down a `properties` or `items` applicator.
    pub fn validate<'i>(&'a self, instance: &'i Value) -> Result<(), ValidationError<'i, 'a>> {
        self.continue_validation(instance, &mut HashSet::new())
    }

    /// Continues Validation of a JSON instance at the same location.
    pub fn continue_validation<'i>(
        &'a self,
        instance: &'i Value,
        evaluated_props: &mut HashSet<&'i str>,
    ) -> Result<(), ValidationError<'i, 'a>> {
        match self {
            Subschema::Bool(b) => {
                if *b {
                    Ok(())
                } else {
                    Err(ValidationError { instance, subschema: self })
                }
            }
            Subschema::Object(vec) => {
                let mut validated_props = HashSet::new();
                let mut sub_evaluated_props = HashSet::new();
                for keyword in vec {
                    match keyword {
                        SchemaKeyword::Ref(r) => r
                            .as_ref()
                            .get()
                            .expect("Unresolved refs are not expected during validation.")
                            .continue_validation(instance, &mut sub_evaluated_props)?,
                        SchemaKeyword::Assertion(a) => a.validate(instance, self)?,
                        SchemaKeyword::Applicator(a) => a.validate(
                            instance,
                            self,
                            &mut validated_props,
                            &mut sub_evaluated_props,
                        )?,
                    }
                }
                evaluated_props.extend(sub_evaluated_props);
                Ok(())
            }
        }
    }

    fn from_object(
        object_map: &'a Map<String, Value>,
        ref_resolver: &'b RefResolver<'a>,
    ) -> Result<Self, SchemaError<'a>> {
        let mut result = vec![];
        let mut additional_props_kw = None;
        let mut unevaluated_props_kw = None;
        for (k, v) in object_map {
            let keyword = match k.as_str() {
                // Core
                "$ref" => SchemaKeyword::Ref(ref_resolver.resolve(v.try_str()?)?),
                // Assertions
                "type" => SchemaKeyword::Assertion(SchemaAssertion::try_new_type(v)?),
                "enum" => SchemaKeyword::Assertion(SchemaAssertion::try_new_enum(v)?),
                "const" => SchemaKeyword::Assertion(SchemaAssertion::new_const(v)),
                "pattern" => SchemaKeyword::Assertion(SchemaAssertion::try_new_pattern(v)?),
                "minimum" => SchemaKeyword::Assertion(SchemaAssertion::try_new_min(v)?),
                "exclusiveMinimum" => SchemaKeyword::Assertion(SchemaAssertion::try_new_xmin(v)?),
                "maximum" => SchemaKeyword::Assertion(SchemaAssertion::try_new_max(v)?),
                "exclusiveMaximum" => SchemaKeyword::Assertion(SchemaAssertion::try_new_xmax(v)?),
                "minItems" => SchemaKeyword::Assertion(SchemaAssertion::try_new_min_items(v)?),
                "maxItems" => SchemaKeyword::Assertion(SchemaAssertion::try_new_max_items(v)?),
                "uniqueItems" => {
                    SchemaKeyword::Assertion(SchemaAssertion::try_new_unique_items(v)?)
                }
                "required" => SchemaKeyword::Assertion(SchemaAssertion::try_new_required(v)?),
                // Applicators
                "oneOf" => {
                    SchemaKeyword::Applicator(SchemaApplicator::try_new_one_of(v, ref_resolver)?)
                }
                "anyOf" => {
                    SchemaKeyword::Applicator(SchemaApplicator::try_new_any_of(v, ref_resolver)?)
                }
                "allOf" => {
                    SchemaKeyword::Applicator(SchemaApplicator::try_new_all_of(v, ref_resolver)?)
                }
                "not" => SchemaKeyword::Applicator(SchemaApplicator::try_new_not(v, ref_resolver)?),
                "if" => SchemaKeyword::Applicator(SchemaApplicator::try_new_if_then_else(
                    v,
                    object_map.get("then"),
                    object_map.get("else"),
                    ref_resolver,
                )?),
                "then" | "else" => continue, // handled in the if arm
                "properties" => SchemaKeyword::Applicator(SchemaApplicator::try_new_properties(
                    v,
                    ref_resolver,
                )?),
                "additionalProperties" => SchemaKeyword::Applicator(
                    SchemaApplicator::try_additional_properties(v, ref_resolver)?,
                ),
                "items" => {
                    SchemaKeyword::Applicator(SchemaApplicator::try_new_items(v, ref_resolver)?)
                }
                "unevaluatedProperties" => SchemaKeyword::Applicator(
                    SchemaApplicator::try_unevaluated_properties(v, ref_resolver)?,
                ),
                k if INGORED_KEYWORDS.contains(&k) => continue, //ignored
                k => return Err(SchemaError::UnkownKeyword(k)),
            };
            match keyword {
                SchemaKeyword::Applicator(SchemaApplicator::AdditionalProperties(_)) => {
                    additional_props_kw = Some(keyword)
                }
                SchemaKeyword::Applicator(SchemaApplicator::UnevaluatedProperties(_)) => {
                    unevaluated_props_kw = Some(keyword)
                }
                _ => result.push(keyword),
            }
        }

        // Orders the keyword so that additionalProperties and unevaluatedProperties
        // keywords are put last (in that order) This makes it ready for validation, so
        // that additionalProperties and  are validated at the end.
        if let Some(kw) = additional_props_kw {
            result.push(kw)
        }
        if let Some(kw) = unevaluated_props_kw {
            result.push(kw)
        }

        Ok(Subschema::Object(result))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_read_bool_subschema() {
        let v = json!(true);
        assert!(matches!(
            Subschema::from_json(&v, &RefResolver::new(&v)),
            Ok(Subschema::Bool(true))
        ));
    }

    #[test]
    fn test_read_subschema_ignored_keyword() {
        let v = json!({INGORED_KEYWORDS[0]: 42});
        assert!(matches!(Subschema::from_json(&v, &RefResolver::new(&v)), Ok(_)));
    }

    #[test]
    fn test_read_subschema_unknown_keyword() {
        let v = json!({"someKey": 42});
        assert!(matches!(Subschema::from_json(&v, &RefResolver::new(&v)), Err(_)));
    }
}
