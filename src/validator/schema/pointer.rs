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

use std::cell::{OnceCell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use super::SchemaError::{self, UnresolvableRef};
use super::Subschema;
use serde_json::Value;

pub struct RefResolver<'a> {
    root_value: &'a Value,
    cache: RefCell<HashMap<String, Rc<OnceCell<Subschema<'a>>>>>,
}

impl<'a> RefResolver<'a> {
    pub fn new(root_value: &'a Value) -> Self {
        Self { root_value, cache: RefCell::new(HashMap::new()) }
    }

    /// Resolves a [super::SchemaKeyword::Ref] pointer. The result is cached and
    /// reused in subsequent calls.
    pub fn resolve<'p>(
        &self,
        pointer: &'p str,
    ) -> Result<Rc<OnceCell<Subschema<'a>>>, SchemaError<'p>>
    where
        'a: 'p,
    {
        if let Some(result) = self.cache.borrow().get(pointer) {
            // The value can still be None at this point, which means we're within a
            // recursive ref resolution. When we get out of those recursions, the actua/l
            // Subschemas will be present.
            return Ok(Rc::clone(result));
        }

        // Insert a pending entry first, to break potential Ref cycles.
        let entry = Rc::new(OnceCell::new());
        self.cache.borrow_mut().insert(pointer.to_owned(), Rc::clone(&entry));

        // Value.pointer parameter should start with '/'. So we remove the initial '#'
        // character
        let resolved_value =
            self.root_value.pointer(&pointer[1..]).ok_or(UnresolvableRef(pointer))?;
        assert!(
            entry.set(Subschema::from_json(resolved_value, self)?).is_ok(),
            "Expected the entry to be unset."
        );
        Ok(Rc::clone(&entry))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_resolve() {
        let v = json!({
            "$defs": {
                "p1": {
                    "type": "integer"
                },
            }
        });

        let resolver = RefResolver::new(&v);
        let result = resolver.resolve("#/$defs/p1").unwrap();
        assert!(result.get().unwrap().validate(&json!(42)).is_ok());
        assert!(result.get().unwrap().validate(&json!("42")).is_err());

        assert!(matches!(resolver.resolve("#/$defs/nonexistentnode"), Err(UnresolvableRef(_))));
    }

    #[test]
    fn test_resolve_recursive() {
        let v = json!({
            "$defs": {
                "p1": {
                    "properties": {
                        "foo": {
                            "type": "object",
                            "$ref": "#/$defs/p2"
                        }
                    }
                },
                "p2": {
                    "properties": {
                        "baz": {
                            "const": 42
                        }
                    }
                }
            }
        });

        let resolver = RefResolver::new(&v);
        let result = resolver.resolve("#/$defs/p1").unwrap();
        assert!(result.get().unwrap().validate(&json!({"foo":{"baz": 42}})).is_ok());

        assert!(result.get().unwrap().validate(&json!({"foo":{"baz": "42"}})).is_err());
    }

    #[test]
    fn test_resolve_with_cycle() {
        let v = json!({
            "$defs": {
                "p1": {
                    "properties": {
                        "foo": {
                            "type": "integer"
                        },
                        "bar": {
                            "$ref": "#/$defs/p2"
                        }
                    }
                },
                "p2": {
                    "properties": {
                        "baz": {
                            "$ref": "#/$defs/p1"
                        },
                    }
                }
            }
        });

        let resolver = RefResolver::new(&v);
        let result = resolver.resolve("#/$defs/p1").unwrap();
        assert!(result
            .get()
            .unwrap()
            .validate(&json!({"foo":42,"bar":{"baz":{"foo":43}}}))
            .is_ok());

        assert!(result
            .get()
            .unwrap()
            .validate(&json!({"foo":42,"bar":{"baz":{"foo":43.1}}}))
            .is_err());
    }
}
