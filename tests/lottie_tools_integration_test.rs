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

//! Lottie Tools integration tests.
#![cfg(test)]

mod spec;
mod suite;
use std::path::{Path, PathBuf};
use std::{fs::File, io::BufReader};

use lottie_tools::validator::Schema;
use serde_json::Value;
use spec::expect_failure;
use spec::expect_success;
use spec::expect_success_sanitized;
use suite::test_suite;

// TOOD: b/381985258 - Implement missing assertions

const UNIMPLEMENTED_UNIQUE_ITEM_TESTS: &[&str] = &[
    "uniqueItems with an array of items", // uses prefixItems
    "uniqueItems with an array of items and additionalItems=false", // uses prefixItems
    "uniqueItems=false with an array of items", // uses prefixItems
    "uniqueItems=false with an array of items and additionalItems=false", // uses prefixItems
];

const UNIMPLEMENTED_PROPERTIES_TESTS: &[&str] =
    &["properties, patternProperties, additionalProperties interaction"]; // uses patternProperties

// TODO: b/381985258 - Fix Value euqality for Numbers
const UNIMPLEMENTED_ENUM_TESTS: &[&str] = &[
    "enum with 0 does not match false",     // 0 == 0.0
    "enum with [0] does not match [false]", // 0 == 0.0
    "enum with 1 does not match true",      // 1 == 1.0
    "enum with [1] does not match [true]",
];

// TODO: b/381985258 - Fix Value euqality for Numbers
const UNIMPLEMENTED_CONST_TESTS: &[&str] = &[
    "const with 0 does not match other zero-like types", // 0 == 0.0
    "const with 1 does not match true",                  // 1 == 1.0
    "const with -2.0 matches integer and float types",   // -2 == -2.0
    "float and integers are equal up to 64-bit representation limits", /* 9007199254740992 ==
                                                          * 9007199254740992.0 */
];

const UNIMPLEMENTED_ANY_OF_TESTS: &[&str] = &[
    "anyOf with base schema", // Uses maxLength/minLength
];

const UNIMPLEMENTED_ONE_OF_TESTS: &[&str] = &[
    "oneOf with base schema", // Uses maxLength/minLength
];

const UNIMPLEMENTED_ALL_OF_TESTS: &[&str] = &[
    "allOf combined with anyOf, oneOf", // Uses multipleOf
];

const UNIMPLEMENTED_ITEMS_TESTS: &[&str] = &[
    "items and subitems",                           // Uses prefixItems
    "prefixItems with no additional items allowed", // Uses prefixItems
    "items does not look in applicators, valid case",
    "prefixItems validation adjusts the starting index for items",
    "items with heterogeneous array",
];

const UNIMPLEMENTED_IF_THEN_ELSE_TESTS: &[&str] = &[
    "if and else without then",                      // Uses multipleOf
    "validate against correct branch, then vs else", // Uses multipleOf
    "non-interference across combined schemas",      // Uses multipleOf
    "if appears at the end when serialized (keyword processing sequence)", // Uses maxLength
];

const UNIMPLEMENTED_ADDITIONAL_PROPERTIES_TESTS: &[&str] = &[
    "additionalProperties being false does not allow other properties", // uses patternProperties
    "non-ASCII pattern with additionalProperties",                      // uses patternProperties
    "additionalProperties with propertyNames",                          // uses propertyNames
    "dependentSchemas with additionalProperties",                       // uses dependentSchemas
];

const UNIMPLEMENTED_REF_TESTS: &[&str] = &[
    "relative pointer ref to array",             // Uses prefixItems
    "escaped pointer ref",                       // Escaped % not supported by Value::pointer
    "remote ref, containing refs itself",        // Uses $id
    "Recursive references between schemas",      // Uses $id
    "refs with quote",                           // Escaped " not supported by Value::pointer
    "refs with relative uris and defs",          // Uses $id
    "relative refs with absolute uris and defs", // Uses $id
    "$id must be resolved against nearest parent, not just immediate parent", // Uses $id
    "order of evaluation: $id and $ref",         // Uses $id
    "order of evaluation: $id and $anchor and $ref", // Uses $id and $anchor
    "simple URN base URI with $ref via the URN", // Uses URN/$id
    "simple URN base URI with JSON pointer",     // Uses URN/$id
    "URN base URI with NSS",                     // Uses URN/$id
    "URN base URI with r-component",             // Uses URN/$id
    "URN base URI with q-component",             // Uses URN/$id
    "URN base URI with URN and JSON pointer ref", // Uses URN/$id
    "URN base URI with URN and anchor ref",      // Uses URN/$id
    "URN ref with nested pointer ref",           // Uses URN/$id
    "ref to if",                                 // Uses $id
    "ref to then",                               // Uses $id
    "ref to else",                               // Uses $id
    "ref with absolute-path-reference",          // Uses $id
];

const UNIMPLEMENTED_UNEVALUATED_PROPS_TESTS: &[&str] = &[
    "unevaluatedProperties schema", // Uses minLength
    "unevaluatedProperties with adjacent patternProperties", // Uses patternProperties
    "unevaluatedProperties with nested patternProperties", // Uses patternProperties
    "unevaluatedProperties with nested unevaluatedProperties", // Uses maxLength
    "unevaluatedProperties with dependentSchemas", // Uses dependentSchemas
    "unevaluatedProperties with $dynamicRef", // Uses $id
    "dynamic evalation inside nested refs", // Uses patternProperties
    "unevaluatedProperties not affected by propertyNames", // Uses propertyNames
    "unevaluatedProperties can see annotations from if without then and else", /* Uses patternProperties */
    "dependentSchemas with unevaluatedProperties", //Uses depndendSchemas
];

test_suite!(type);
test_suite!(enum, UNIMPLEMENTED_ENUM_TESTS);
test_suite!(const, UNIMPLEMENTED_CONST_TESTS);
test_suite!(pattern);
test_suite!(minimum);
test_suite!(exclusiveMinimum);
test_suite!(maximum);
test_suite!(exclusiveMaximum);
test_suite!(maxItems);
test_suite!(minItems);
test_suite!(uniqueItems, UNIMPLEMENTED_UNIQUE_ITEM_TESTS);
test_suite!(required);
test_suite!(anyOf, UNIMPLEMENTED_ANY_OF_TESTS);
test_suite!(oneOf, UNIMPLEMENTED_ONE_OF_TESTS);
test_suite!(allOf, UNIMPLEMENTED_ALL_OF_TESTS);
test_suite!(not);
test_suite!(if_then_else, UNIMPLEMENTED_IF_THEN_ELSE_TESTS);
test_suite!(items, UNIMPLEMENTED_ITEMS_TESTS);
test_suite!(properties, UNIMPLEMENTED_PROPERTIES_TESTS);
test_suite!(additionalProperties, UNIMPLEMENTED_ADDITIONAL_PROPERTIES_TESTS);
test_suite!(ref, UNIMPLEMENTED_REF_TESTS);
test_suite!(infinite_loop_detection);
test_suite!(unevaluatedProperties, UNIMPLEMENTED_UNEVALUATED_PROPS_TESTS);

#[test]
fn test_spec() {
    let schema_json: Value = serde_json::from_reader(BufReader::new(
        File::open("third_party/lottie_spec/v1.schema.json").unwrap(),
    ))
    .unwrap();
    let schema = Schema::from_json(&schema_json).unwrap();
    expect_success!(schema, "tests/spec/valid");
    expect_success_sanitized!(schema, "tests/spec/valid");
    expect_success!(schema, "tests/spec/profile_invalid");
    expect_success!(schema, "tests/spec/profile_warning");
    expect_failure!(schema, "tests/spec/invalid");
}

#[test]
fn test_strict_spec() {
    let schema_json: Value = serde_json::from_reader(BufReader::new(
        File::open("third_party/lottie_spec/v1.strict.schema.json").unwrap(),
    ))
    .unwrap();
    let schema = Schema::from_json(&schema_json).unwrap();
    expect_failure!(schema, "tests/spec/valid");
    expect_success_sanitized!(schema, "tests/spec/valid");
    expect_failure!(schema, "tests/spec/invalid");
}

#[test]
fn test_profile() {
    let schema_json: Value = serde_json::from_reader(BufReader::new(
        File::open("data/wear_profile/v1.schema.json").unwrap(),
    ))
    .unwrap();
    let schema = Schema::from_json(&schema_json).unwrap();
    expect_success!(schema, "tests/spec/valid");
    expect_success!(schema, "tests/spec/profile_warning");
    expect_failure!(schema, "tests/spec/profile_invalid");
}

#[test]
fn test_profile_performance_warning() {
    let schema_json: Value = serde_json::from_reader(BufReader::new(
        File::open("data/wear_profile/v1-performance-warning.schema.json")
            .unwrap(),
    ))
    .unwrap();
    let schema = Schema::from_json(&schema_json).unwrap();
    expect_success!(schema, "tests/spec/valid");
    expect_failure!(schema, "tests/spec/profile_warning");
}
