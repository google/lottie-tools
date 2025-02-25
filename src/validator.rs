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

//! Validator for Lottie files.

use serde_json::Value;

mod schema;
pub use schema::Schema;

/// Validates a JSON instace against a JSON schema.
pub fn validate<S: AsRef<str>>(schema: S, asset: S) -> bool {
    // TODO: Don't panic
    validate_json(
        &serde_json::from_str(schema.as_ref()).unwrap(),
        &serde_json::from_str(asset.as_ref()).unwrap(),
    )
}

/// Validates a JSON instace against a JSON schema.
pub fn validate_json(schema: &Value, asset: &Value) -> bool {
    // TODO: b/381985258 - Return full failure result
    match Schema::from_json(schema) {
        Ok(s) => s.validate(&asset).is_ok(),
        Err(e) => panic!("{}", e),
    }
}
