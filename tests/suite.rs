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

#![cfg(test)]

use std::fs::File;
use std::io::BufReader;

use lottie_tools::validator::validate_json;
use serde::Deserialize;
use serde_json::Value;

/// When called with parameter `foo`, creates a test method called
/// `test_draft2020_12_foo` that runs the test suite for the file `foo.json`
macro_rules! test_suite {
    ($name:ident) => {
        test_suite!($name, &[]);
    };
    ($name:ident, $excluded_tests:expr) => {
        paste::paste! {
            #[allow(non_snake_case)]
            #[test]
            fn [<test_draft2020_12_ $name>]() {
                let file_path = &format!(
                    "third_party/json_schema_test_suite/tests/latest/{}.json",
                    stringify!($name).replace("_", "-"));
                let f = std::path::Path::new(file_path);
                for (desc, test_cases) in suite::test_path(f.to_str().unwrap(), $excluded_tests) {
                    println!("<{}>", desc);
                    for (test_desc, passed) in test_cases {
                        println!("  <{}>", test_desc);
                        assert!(passed, "Failed for <{}>::<{}>", desc, test_desc);
                    }
                }
            }
        }
    };
}

pub(crate) use test_suite;

pub(crate) fn test_path(
    file_path: &str,
    excluded_tests: &[&str],
) -> Vec<(String, Vec<(String, bool)>)> {
    let input = File::open(file_path).unwrap();
    let test_cases: Vec<TestCase> = serde_json::from_reader(BufReader::new(input)).unwrap();

    test_cases
        .into_iter()
        .filter(|tc| !excluded_tests.contains(&tc.description.as_ref()))
        .map(|tc| tc.test())
        .collect()
}

#[derive(Deserialize)]
struct TestCase {
    description: String,
    schema: Value,
    tests: Vec<Test>,
}

impl TestCase {
    fn test(self) -> (String, Vec<(String, bool)>) {
        (
            self.description,
            self.tests
                .into_iter()
                .map(|t| (t.description, validate_json(&self.schema, &t.data) == t.valid))
                .collect(),
        )
    }
}

#[derive(Deserialize)]
struct Test {
    description: String,
    data: Value,
    valid: bool,
}
