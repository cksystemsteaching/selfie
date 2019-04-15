import unittest
import sys
import os
from os import system
from time import time

from unittest.mock import patch
from grader.tests.lib import Console, for_all_test_results
from grader.self import execute, TimeoutException, test_base
import grader.self as grader

class TestExecutionTimeout(unittest.TestCase):

  original_execute = execute

  @classmethod
  def setUpClass(self):
    system('make selfie >/dev/null 2>&1')

  def test_timeout(self):
    start = time()

    grader.home_path = './'

    self.assertRaises(TimeoutException, TestExecutionTimeout.original_execute, 
      './selfie -c grader/tests/sleep-forever.c -m 10', 3)

    self.assertLess(time() - start, 4)

  def execute_mock(self, command, timeout=10):
    return TestExecutionTimeout.original_execute(command, timeout=0)

  def check_output(self, result, msg):
    self.assertFalse(result)

  @patch('grader.self.execute')
  def test_result_of_timed_out_test(self, mock):
    mock.side_effect = self.execute_mock

    with Console() as console:
      test_base()
      output = console.get_output()

    for_all_test_results(output, self.check_output)

if __name__ == '__main__':
  unittest.main()