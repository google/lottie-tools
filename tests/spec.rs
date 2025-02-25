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

macro_rules! expect_success {
    ($schema:ident, $dir_path: literal) => {
        let failures: Vec<String> = spec::validate_dir(&$schema, $dir_path, &[], false)
            .filter_map(|(f, result)| result.err().map(|e| format!("{f:=>40}:\n{e}")))
            .collect();
        assert!(
            failures.is_empty(),
            "Expected validation sucess. But these files failed to validate:\n{}",
            failures.join("\n\n")
        )
    };
}

macro_rules! expect_success_sanitized {
    ($schema:ident, $dir_path: literal) => {
        let failures: Vec<String> = spec::validate_dir(&$schema, $dir_path, &[], true)
            .filter_map(|(f, result)| result.err().map(|e| format!("{f:=>40}:\n{e}")))
            .collect();
        assert!(
            failures.is_empty(),
            "Expected strict validation sucess. But these files failed to validate:\n{}",
            failures.join("\n\n")
        )
    };
}

macro_rules! expect_failure {
    ($schema:ident, $dir_path: literal) => {
        expect_failure!($schema, $dir_path, &[]);
    };
    ($schema:ident, $dir_path: literal, $excluded_files:expr) => {
        let successes: Vec<String> =
            spec::validate_dir(&$schema, $dir_path, $excluded_files, false)
                .filter_map(|(f, result)| result.ok().map(|_| f))
                .collect();
        assert!(
            successes.is_empty(),
            "Expected validation failures. But these files validated successfully:\n{}",
            successes.join("\n")
        )
    };
}

pub(crate) use expect_failure;
pub(crate) use expect_success;
pub(crate) use expect_success_sanitized;

use lottie_tools::sanitizer::sanitize_lottie;

pub fn validate_dir<'a>(
    schema: &'a lottie_tools::validator::Schema<'a>,
    dir_path: &str,
    excluded_files: &'a [&str],
    sanitize: bool,
) -> impl Iterator<Item = (String, Result<(), String>)> + 'a {
    std::fs::read_dir(dir_path).unwrap().filter_map(move |f| {
        let Ok(f) = f else {
            return None;
        };
        let Ok(t) = f.file_type() else {
            return None;
        };
        if t.is_dir() || (t.is_file() && !f.file_name().to_str()?.ends_with(".json")) {
            return None;
        }
        if excluded_files.contains(&f.file_name().to_str()?) {
            return None;
        }
        let path = f.path();
        let mut lottie_json: serde_json::Value = serde_json::from_reader(std::io::BufReader::new(
            std::fs::File::open(path.to_str().unwrap()).unwrap(),
        ))
        .unwrap();
        if sanitize {
            sanitize_lottie(&mut lottie_json);
        }
        let schema_result = schema.validate(&lottie_json);
        Some((f.file_name().to_str()?.into(), schema_result.map_err(|e| e.to_string())))
    })
}
