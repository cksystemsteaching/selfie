import unittest
from unittest.mock import patch
import sys
import os
from grader.tests.lib import assemble_for_selfie, Console, for_all_test_results, list_files
from grader.self import execute, main, defined_tests
import grader.self

class TestInstructionEncoding(unittest.TestCase):

  @classmethod
  def setUpClass(self):
    self.instructions = list(map(lambda f: f[:-2], list_files('grader/tests/instructions', extension='.s')))

  def execute_mock(self, command):
    if '.tmp.bin' in command:
      for instruction in self.instructions:
        if instruction in command:
          assemble_for_selfie('instructions/' + instruction + '.s')

    return (0, '', '')

  def check_encoding_results(self, result, msg):
    if 'RISC-V encoding' in msg:
      self.assertTrue(result, 'following encoding test passed: "' + msg + '"')

  @patch('grader.self.execute')
  def test_instruction_encoding(self, mock):
    mock.side_effect = lambda c: self.execute_mock(c)

    with Console() as console:
      main([sys.argv[0]] + list(map(lambda t: t[0], defined_tests)))
      output = console.get_output()

    for_all_test_results(output, self.check_encoding_results)

if __name__ == '__main__':
  unittest.main()