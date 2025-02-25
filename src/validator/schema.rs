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

//! Representation of a JSON Schema. Note that this is built to be used for
//! Lottie schema. As a result some assumptions have been made and features that
//! are not used by Lottie schema specification might not be implemented.

use pointer::RefResolver;
use serde_json::Value;
use subschema::{SchemaKeyword, Subschema};
use thiserror::Error;

mod applicator;
mod assertion;
mod pointer;
mod subschema;
mod utils;

#[derive(Debug, Error)]
pub enum SchemaError<'a> {
    #[error("Unkown instance type <{0}>.")]
    UnkownInstanceType(&'a str),
    #[error("Expected {expected}, but received <{value}>.")]
    UnexpectedValue { expected: &'a str, value: &'a Value },
    #[error("Unknown keyword <{0}>.")]
    UnkownKeyword(&'a str),
    #[error(transparent)]
    RegexError(#[from] regex::Error),
    #[error("Failed to resolve pointer <{0}>")]
    UnresolvableRef(&'a str),
}

#[derive(Debug, Error)]
#[error("Node {instance} failed to validate against subschema {subschema:?}")]
pub struct ValidationError<'i, 's> {
    instance: &'i Value,
    subschema: &'s Subschema<'s>,
}

/// Represents a schema file.
pub struct Schema<'a> {
    // ref_resolver: Rc<RefResolver<'a>>,
    root_subschema: Subschema<'a>,
}

impl<'a> Schema<'a> {
    /// Creates a new [Schema] from a root [Value]. The result can be later to
    /// validate JSON instances against this schema.
    ///
    /// ```
    /// # use serde_json::json;
    /// # use lottie_tools::validator::Schema;
    /// let s = Schema::from_json(&json!(true)).unwrap();
    /// assert!(s.validate(&json!(42)).is_ok());
    /// ```
    pub fn from_json(input: &'a Value) -> Result<Self, SchemaError<'a>> {
        let ref_resolver = RefResolver::new(input);
        let root_subschema = Subschema::from_json(input, &ref_resolver)?;

        Ok(Schema { root_subschema })
    }

    /// Validates a JSON [Value] against this [Schema].
    ///
    /// ```
    /// # use serde_json::json;
    /// # use lottie_tools::validator::Schema;
    /// let s = Schema::from_json(&json!(true)).unwrap();
    /// assert!(s.validate(&json!(42)).is_ok());
    /// ```
    pub fn validate<'i>(&'a self, instance: &'i Value) -> Result<(), ValidationError<'i, 'a>> {
        self.root_subschema.validate(instance)
    }
}
