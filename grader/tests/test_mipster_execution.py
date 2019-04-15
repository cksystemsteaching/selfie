import unittest
from unittest.mock import patch
import sys

from grader.tests.lib import Console, compile_with_gcc_and_run
from grader.self import main, defined_tests
import grader.self

class TestMipsterExecution(unittest.TestCase):

  def setUp(self):
    patcher = patch('grader.self.print_loud')
    self.addCleanup(patcher.stop)
    self.mock_foo = patcher.start()

  def mipster_execution_mock(self, file, result, msg):
    if 'invalid' not in file:
      return_value = compile_with_gcc_and_run(file)

      self.assertEqual(result, return_value, 'compiling ' + file + ' with gcc and running the programming gives the expected result')

  @patch('grader.self.test_mipster_execution')
  def test_mipster_execution_results(self, test_mipster_execution_mock):
    test_mipster_execution_mock.side_effect = self.mipster_execution_mock

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