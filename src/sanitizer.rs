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

use serde_json::{json, Value};

// TODO Verify these don't need to be targeted
// TODO "l" and "np" should verify matches array length?
// TODO remvoing "td" may change behavior

// Refer to official lottie docs (lottie.github.io) and community docs
// (https://lottiefiles.github.io/lottie-docs/) for more information on these
// properties.
const SANITIZE_KEYS: &[&str] = &["ix", "mn", "cix", "np", "l", "td", "cl", "ct"];
const SANITIZE_KEYS_IF_ROOT: &[&str] = &["v", "props"];
const SANITIZE_KEYS_IF_NOT_LAYER: &[&str] = &["ind"];
const SANITIZE_KEYS_IF_ASSET: &[&str] = &["fr"];
const SANITIZE_KEYS_IF_NOT_PRECOMP: &[&str] = &["sr", "st"];
const SANITIZE_KEYS_IF_VAL_IS_ZERO: &[&str] = &["ddd", "bm", "ao"];

pub fn sanitize_lottie(lottie: &mut Value) {
    if let Value::Object(ref mut o) = lottie {
        o.retain(|k, _| !SANITIZE_KEYS_IF_ROOT.contains(&k.as_str()));
    }

    // TODO we probably don't want to run slots through this as they have
    // user defined keys
    sanitize_value(lottie);
}

fn sanitize_value(val: &mut Value) {
    match val {
        Value::Object(o) => {
            o.retain(|k, _| !SANITIZE_KEYS.contains(&k.as_str()));

            o.retain(|k, v| {
                !(SANITIZE_KEYS_IF_VAL_IS_ZERO.contains(&k.as_str()) && *v == json!(0))
            });

            if let Some(Value::Number(n)) = o.get("ty") {
                // Only layers have ty:number property
                if let Some(ty) = n.as_i64() {
                    if ty != 0 {
                        o.retain(|k, _| !SANITIZE_KEYS_IF_NOT_PRECOMP.contains(&k.as_str()));
                    }
                }
            } else {
                o.retain(|k, _| !SANITIZE_KEYS_IF_NOT_LAYER.contains(&k.as_str()));
            }

            if let Some(Value::String(s)) = o.get("id") {
                o.retain(|k, _| !SANITIZE_KEYS_IF_ASSET.contains(&k.as_str()));
            }

            for (_, value) in o {
                sanitize_value(value);
            }
        }
        Value::Array(a) => {
            for entry in a {
                sanitize_value(entry);
            }
        }
        _ => (),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_root_keys() {
        let mut lottie = json!({
            "v": "5.1.12",
            "layers": [],
            "props": {
                "testprop": "testvalue"
            },
            "subobj": {
                "v": "5.1.12",
                "props": {
                    "testprop": "testvalue"
                },
            }
        });
        let sanitized_lottie = json!({
            "layers": [],
            "subobj": {
                "v": "5.1.12",
                "props": {
                    "testprop": "testvalue"
                },
            }
        });

        sanitize_lottie(&mut lottie);

        assert_eq!(lottie, sanitized_lottie);
    }

    #[test]
    fn test_all_keys() {
        let mut lottie = json!({
            "ix": 1,
            "mn": "test",
            "cix": 1,
            "np": 1,
            "l": 1,
            "td": 1,
            "cl": 1,
            "layers": [{
                "ix": 1,
                "mn": "test",
                "cix": 1,
                "np": 1,
                "l": 1,
                "td": 1,
                "cl": 1,
                "ct": 1,
            }],
        });
        let sanitized_lottie = json!({
            "layers": [{}],
        });

        sanitize_lottie(&mut lottie);

        assert_eq!(lottie, sanitized_lottie);
    }

    #[test]
    fn test_not_layer_keys() {
        let mut lottie = json!({
            "ind": 1,
            "layers": [{
                "ty": 1,
                "ind": 2,
                "shapes": [{
                    "ind": 3,
                    "ty": "g"
                }]
            }],
        });
        let sanitized_lottie = json!({
            "layers": [{
                "ty": 1,
                "ind": 2,
                "shapes": [{
                    "ty": "g"
                }]
            }],
        });

        sanitize_lottie(&mut lottie);

        assert_eq!(lottie, sanitized_lottie);
    }

    #[test]
    fn test_not_precomp_keys() {
        let mut lottie = json!({
            "layers": [{
                "ty": 1,
                "sr": 1,
                "st": 1,
            },{
                "ty": 0,
                "sr": 1,
                "st": 1,
            }],
        });
        let sanitized_lottie = json!({
            "layers": [{
                "ty": 1,
            },{
                "ty": 0,
                "sr": 1,
                "st": 1,
            }],
        });

        sanitize_lottie(&mut lottie);

        assert_eq!(lottie, sanitized_lottie);
    }

    #[test]
    fn test_zero_val_keys() {
        let mut lottie = json!({
            "layers": [{
                "ddd": 0,
                "bm": 0,
                "ao": 0,
            },{
                "ddd": 1,
                "bm": 1,
                "ao": 1,
            }],
        });
        let sanitized_lottie = json!({
            "layers": [{
            },{
                "ddd": 1,
                "bm": 1,
                "ao": 1,
            }],
        });

        sanitize_lottie(&mut lottie);

        assert_eq!(lottie, sanitized_lottie);
    }

    #[test]
    fn test_asset_keys() {
        let mut lottie = json!({
            "fr": 30,
            "assets": [{
                "fr": 30,
                "id": "test"
            }],
        });
        let sanitized_lottie = json!({
            "fr": 30,
            "assets": [{
                "id": "test"
            }],
        });

        sanitize_lottie(&mut lottie);

        assert_eq!(lottie, sanitized_lottie);
    }
}
