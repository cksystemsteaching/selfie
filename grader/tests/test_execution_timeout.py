import unittest
import sys
import os
from os import system
from time import time
from pathlib import Path
from unittest.mock import patch

from self import check_self_compilation
from lib.checks import execute, TimeoutException, set_home_path
from tests.utils import CaptureOutput, for_all_test_results

class TestExecutionTimeout(unittest.TestCase):

    def setUp(self):
        os.chdir('..')

    def tearDown(self):
        os.chdir('grader')

    @classmethod
    def setUpClass(self):
        system('cd .. && make selfie >/dev/null 2>&1')

    def test_timeout(self):
        start = time()

        self.assertRaises(TimeoutException, execute,
                        './selfie -c grader/tests/sleep-forever.c -m 10', 3)

        self.assertLess(time() - start, 4)

    def execute_mock(self, command, timeout=10):
        return execute(command, timeout=0)

    def check_output(self, result, msg):
        self.assertFalse(result)

    @patch('lib.checks.execute')
    def test_result_of_timed_out_test(self, mock):
        mock.side_effect = self.execute_mock

        set_home_path(Path('..'))

        with CaptureOutput() as capture:
            check_self_compilation()

            output = capture.get_output()

        for_all_test_results(output, self.check_output)


if __name__ == '__main__':
    unittest.main()
