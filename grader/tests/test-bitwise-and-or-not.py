import unittest
from unittest.mock import patch
import sys
import os

from grader.tests.lib import assemble_for_selfie, Console, for_all_test_results, compile_with_gcc_and_run, compile_with_gcc
from grader.self import DummyWriter, execute, main
import grader.self

class TestBitwiseAndOrNot(unittest.TestCase):

  def mipster_execution_mock(self, file, result, msg):
    if 'invalid' not in file:
      return_value = compile_with_gcc_and_run(file)

      self.assertEqual(result, return_value, 'compiling ' + file + ' with gcc and running the programming gives the expected result')

  @patch('grader.self.test_mipster_execution')
  def test_mipster_execution_results(self, test_mipster_execution_mock):
    test_mipster_execution_mock.side_effect = self.mipster_execution_mock
    
    with Console():
      main([sys.argv[0], 'bitwise-and-or-not'])

  def compilable_mock(self, file, msg, should_succeed=True):
    if 'invalid' in file:
      self.assertFalse(should_succeed)
    if not should_succeed:
      self.assertIn('invalid', file)

    if 'invalid' in file:
      self.assertNotEqual(compile_with_gcc(file), 0, 'compiling ' + file + ' with gcc leads to an error')
    else:
      self.assertEqual(compile_with_gcc(file), 0, 'compiling ' + file + ' with gcc leads to no error')

  @patch('grader.self.test_compilable')
  def test_compilability_of_test_files(self, test_compilable_mock):
  
    test_compilable_mock.side_effect = self.compilable_mock

    with Console():
      main([sys.argv[0], 'bitwise-and-or-not'])

if __name__ == '__main__':
  unittest.main()