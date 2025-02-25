# Copyright 2025 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


import argparse
import json
import os
import pathlib

# This script is used to create a strict schema for lottie.
#
# The strict schema needs to
# 1. Remove unknown properties
#   TODO script doesn't do this yet, was done manually
# 2. Set unevaluatedProperties to false for all subschemas.
#
# The strict schema is used in conjunction with the sanitizer in
# third_party/lottie_tools/src/sanitizer.rs. The sanitizer removes unsupported
# fields from lottie files. By using the strict schema, we can then validate
# the lottie files using the full lottie schema.

# TODO integrate with blaze build

# Ignored subschemas
# With how inheritance is achieved in json schema with allOf, we can't have
# strict schemas be extended, as the additional fields of the child would cause
# the parent schema to fail validation.
ignored_subschemas = [
    'visual-object',
    'asset',
    'composition',
    'visual-layer',
    'layer',
    'vector-keyframe',
    'base-keyframe',
    'shape',
    'graphic-element',
    'modifier',
    'transform',
    'shape-style',
    'slottable-object',
    'slottable-property',
    'base-stroke',
    'base-gradient',
]


def strictify_fields(
    json_data: dict[str, any],
):
  """Strictify the fields in the json data."""
  for module_data in json_data['$defs'].values():
    for attr, attr_data in module_data.items():
      if (
          attr_data.get('type') == 'object'
          and attr not in ignored_subschemas
      ):
        attr_data['unevaluatedProperties'] = False

  return json_data


root = pathlib.Path(__file__).absolute().parent.parent

parser = argparse.ArgumentParser(
    description='Modifies lottie schema to disallow unspeced properties.'
)
parser.add_argument(
    '--input',
    '-i',
    type=pathlib.Path,
    default=root / 'data' / 'lottie_spec' / 'v1.schema.json',
    help='Input file name',
)

parser.add_argument(
    '--output',
    '-o',
    type=pathlib.Path,
    default=root / 'data' / 'lottie_spec' /'v1.strict.schema.json',
    help='Output file name',
)

args = parser.parse_args()
input_path: pathlib.Path = args.input
output_path: pathlib.Path = args.output

with open(input_path) as file:
  schema_json = json.load(file)

strictify_fields(schema_json)

os.makedirs(output_path.parent, exist_ok=True)

with open(output_path, 'w') as file:
  json.dump(schema_json, file, indent=4)
