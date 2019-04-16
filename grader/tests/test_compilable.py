import unittest
from unittest.mock import patch
import sys
import os

from grader.tests.lib import Console, compile_with_gcc
from grader.self import main, defined_tests
import grader.self

class TestCompilable(unittest.TestCase):

  def setUp(self):
    patcher = patch('grader.self.print_loud')
    self.addCleanup(patcher.stop)
    self.mock_foo = patcher.start()

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

    tests = list(map(lambda t: t[0], defined_tests))
    tests.remove('assembler-1')
    tests.remove('assembler-2')
    tests.remove('concurrent-machines')
    tests.remove('fork-wait')
    tests.remove('lock')
    tests.remove('thread')
    tests.remove('treiber-stack')

    with Console():
      main([sys.argv[0]] + tests)

if __name__ == '__main__':
  unittest.main()