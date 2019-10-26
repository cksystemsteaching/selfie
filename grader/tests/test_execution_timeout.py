import unittest
import sys
import os
from os import system
from time import time
from unittest.mock import patch

from self import test_self_compilation
from lib.runner import execute, TimeoutException
from tests.utils import Console, for_all_test_results

class TestExecutionTimeout(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        system('make selfie >/dev/null 2>&1')

    def insert_home_path_mock(self, command):
        return command

    @patch('lib.runner.insert_home_path')
    def test_timeout(self, mock):
        mock.side_effect = self.insert_home_path_mock

        start = time()

        self.assertRaises(TimeoutException, execute,
                          '../selfie -c tests/sleep-forever.c -m 10', 3)

        self.assertLess(time() - start, 4)

    def execute_mock(self, command, timeout=10):
        return execute(command, timeout=0)

    def check_output(self, result, msg):
        self.assertFalse(result)

    @patch('lib.runner.execute')
    def test_result_of_timed_out_test(self, mock):
        mock.side_effect = self.execute_mock

        with Console() as console:
            test_self_compilation()

            output = console.get_output()

        for_all_test_results(output, self.check_output)


if __name__ == '__main__':
    unittest.main()
