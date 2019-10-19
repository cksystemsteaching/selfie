import unittest
from unittest.mock import patch
import sys
import os

from grader.tests.lib import Console, compile_with_gcc
from grader.self import main, defined_tests

class TestCompilable(unittest.TestCase):

  def setUp(self):
    patcher = patch('grader.self.print_loud')
    self.addCleanup(patcher.stop)
    self.mock_foo = patcher.start()

  def compilable_mock(self, file, msg, should_succeed=True):
    file_path = 'assignments/' + self.assignment + '/' + file

    if 'invalid' in file:
      self.assertFalse(should_succeed)
    if not should_succeed:
      self.assertIn('invalid', file)

    if 'invalid' in file:
      self.assertNotEqual(compile_with_gcc(file_path), 0, 'compiling ' + file + ' with gcc leads to an error')
    else:
      self.assertEqual(compile_with_gcc(file_path), 0, 'compiling ' + file + ' with gcc leads to no error')

  @patch('grader.self.test_compilable')
  def test_compilability_of_test_files(self, test_compilable_mock):
  
    test_compilable_mock.side_effect = self.compilable_mock

    not_compilable = [
        'assembler-1',
        'assembler-2',
        'concurrent-machines',
        'fork-wait',
        'lock',
        'thread',
        'treiber-stack'
    ]

    tests = [t for t in defined_tests if t[0] not in not_compilable]
    
    for test in tests:
        self.assignment = test[1]

        with Console():
          main([sys.argv[0], test[0]])

if __name__ == '__main__':
  unittest.main()
