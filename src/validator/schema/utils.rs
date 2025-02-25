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

use super::SchemaError::{self, UnexpectedValue};

use serde_json::{Map, Number, Value};

pub(crate) trait TryValue {
    fn try_str(&self) -> Result<&str, SchemaError>;
    fn try_array(&self) -> Result<&Vec<Value>, SchemaError>;
    fn try_number(&self) -> Result<&Number, SchemaError>;
    fn try_bool(&self) -> Result<bool, SchemaError>;
    fn try_object(&self) -> Result<&Map<String, Value>, SchemaError>;
}

impl TryValue for Value {
    fn try_str(&self) -> Result<&str, SchemaError> {
        self.as_str().ok_or(UnexpectedValue { expected: "string", value: self })
    }

    fn try_array(&self) -> Result<&Vec<Value>, SchemaError> {
        self.as_array().ok_or(UnexpectedValue { expected: "array", value: self })
    }

    fn try_number(&self) -> Result<&Number, SchemaError> {
        self.as_number().ok_or(UnexpectedValue { expected: "number", value: self })
    }

    fn try_bool(&self) -> Result<bool, SchemaError> {
        self.as_bool().ok_or(UnexpectedValue { expected: "boolean", value: self })
    }

    fn try_object(&self) -> Result<&Map<String, Value>, SchemaError> {
        self.as_object().ok_or(UnexpectedValue { expected: "object", value: self })
    }
}
