import unittest
from unittest.mock import patch

import yaml

from lib.model_config_parser import ModelConfigParser
import lib.config as cfg
import lib.exceptions as ex

invalid_config_model = """
allowed_formats: [smt2,btor2]

model_types:
  starc:
    64bit:
      riscv: 
        btor2:
          not_a_command: "{rotor} -c {source_file} - 1 -o {output}"
"""


invalid_format_cfg = """
allowed_formats: [smt2,btor2]

model_types:
  starc:
    invalid_format:
      command: "{rotor} -c {source_file} - 1 -o {output}"
"""

invalid_command_placement_cfg = """
allowed_formats: [smt2,btor2]

model_types:
  starc:
    btor2:
    command: "{rotor} -c {source_file} - 1 -o {output}"
"""

invalid_format_cfg = """
allowed_formats: [smt2,btor2]

model_types:
  starc:
    invalid_format:
      command: "{rotor} -c {source_file} - 1 -o {output}"
"""

valid_compilation_model = """
allowed_formats: [smt2,btor2]

model_types:
  compilation: "comp -command"
  starc:
    btor2:
      command: "{rotor} -c {source_file} - 1 -o {output}"
"""


valid_config_models = """
allowed_formats: [smt2,btor2]

model_types:
  starc:
    64bit:
      riscv: 
        btor2:
          command: "{rotor} -c {source_file} - 1 -o {output}"
        smt2: 
          command: "{rotor} -c {source_file}  - 1 -k -smt -nocomments -o {output}"
"""

class TestModelConfigParser(unittest.TestCase):
  @patch.dict(cfg.config, yaml.safe_load(valid_config_models), clear=True)
  def test_valid_model(self):
    config = ModelConfigParser("starc-64bit-riscv-btor2")
    self.assertEqual(config.parse_compile_cmd(), None)
    self.assertEqual(config.parse_format(), "btor2")
    self.assertEqual(config.parse_model_generation_cmd(),"{rotor} -c {source_file} - 1 -o {output}" )

  @patch.dict(cfg.config, yaml.safe_load(valid_config_models), clear=True)
  def test_incomplete_model_type(self):
    with self.assertRaises(ex.ConfigFormatError):
      ModelConfigParser("starc-64bit-riscv")
  
  @patch.dict(cfg.config, yaml.safe_load(valid_config_models), clear=True)
  def test_invalid_model_type(self):
    with self.assertRaises(ex.ParsingError):
      ModelConfigParser("starc-64bit-invalid")
  
  @patch.dict(cfg.config, yaml.safe_load(valid_compilation_model), clear=True)
  def test_compilation_parse(self):
    config = ModelConfigParser("starc-btor2")
    self.assertEqual(config.parse_compile_cmd(), "comp -command")

  @patch.dict(cfg.config, yaml.safe_load(invalid_command_placement_cfg), clear=True)
  def test_invalid_command_placement(self):
    with self.assertRaises(ex.ConfigFormatError):
      ModelConfigParser("starc-btor2")

  @patch.dict(cfg.config, yaml.safe_load(invalid_format_cfg), clear=True)
  def test_invalid_format_config(self):
    with self.assertRaises(ex.ConfigFormatError) as cm:
      ModelConfigParser("starc-invalid_format")
    
    exception = cm.exception
    self.assertIn("not an allowed format", str(exception))

