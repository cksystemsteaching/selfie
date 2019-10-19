from unittest import TestCase, main
from unittest.mock import patch
import sys

from grader.tests.lib import Console, compile_with_gcc_and_run
from grader.self import main as grader_main, defined_tests, EXITCODE_ERROR_RANGE
import grader.self

class TestMipsterExecution(TestCase):

  def setUp(self):
    patcher = patch('grader.self.print_loud')
    self.addCleanup(patcher.stop)
    self.mock_foo = patcher.start()

  def mipster_execution_mock(self, file, result, msg):
    self.assertNotIn(result, EXITCODE_ERROR_RANGE, 'The mipster execution result value can also be an Selfie error code')

    if 'invalid' not in file:
      return_value = compile_with_gcc_and_run('assignments/' + self.assignment + '/' + file)

      self.assertEqual(result, return_value, 'compiling ' + file + ' with gcc and running the programming gives the expected result')

  @patch('grader.self.test_mipster_execution')
  def test_mipster_execution_results(self, test_mipster_execution_mock):
    test_mipster_execution_mock.side_effect = self.mipster_execution_mock

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
        grader_main([sys.argv[0], test[0]])


  def hypster_execution_mock(self, file, result, msg):
    self.assertNotIn(result, EXITCODE_ERROR_RANGE, 'The hypster execution result value can also be an Selfie error code')

    if 'invalid' not in file:
      return_value = compile_with_gcc_and_run('assignments/' + self.assignment + '/' + file)

      self.assertEqual(result, return_value, 'compiling ' + file + ' with gcc and running the programming gives the expected result')


  @patch('grader.self.test_hypster_execution')
  def test_hypster_execution_results(self, test_hypster_execution_mock):
    test_hypster_execution_mock.side_effect = self.hypster_execution_mock

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
        grader_main([sys.argv[0], test[0]])



if __name__ == '__main__':
  main()
