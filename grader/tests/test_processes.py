import unittest
from unittest.mock import patch
import sys
import os

from self import main, assignments
from lib.checks import insert_assignment_path
from tests.utils import CaptureOutput, compile_with_gcc, run_compilable_assignments


class TestProcesses(unittest.TestCase):

    def setUp(self):
        os.chdir("..")

    def tearDown(self):
        os.chdir("grader")

    def insert_assignment_stub(self, command):
        return insert_assignment_path(command) \
            .replace(' -x ', ' -m ') \
            .replace(' -z ', ' -m ') \
            .replace('assignments/', 'grader/tests/assignment_stubs/')

    @patch('lib.checks.insert_assignment_path')
    def test_processes(self, mock):
        mock.side_effect = self.insert_assignment_stub

        with CaptureOutput() as capture:
            main([sys.argv[0], 'processes'])

            self.assertIs('2', capture.get_loud_output())


if __name__ == '__main__':
    unittest.main()
