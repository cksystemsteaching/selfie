import unittest
from unittest.mock import patch
import sys
import os

from self import main, assignments, name, test, directory
from lib.runner import insert_home_path
from tests.utils import Console, compile_with_gcc, run_compilable_assignments


class TestConcurrentMachines(unittest.TestCase):

    def setUp(self):
        os.chdir("..")

    def tearDown(self):
        os.chdir("grader")

    def insert_assignment_stub(self, command):
        return insert_home_path(command) \
            .replace(' -x ', ' -m ') \
            .replace(' -z ', ' -m ') \
            .replace('grader/grader/assignments/', 'grader/tests/assignment_stubs/')

    @patch('lib.runner.insert_home_path')
    def test_concurrent_machines(self, mock):
        mock.side_effect = self.insert_assignment_stub

        with patch('lib.grade.print_loud') as print_mock:
            main([sys.argv[0], 'concurrent-machines'])

            print_mock.assert_any_call('2', end='')


if __name__ == '__main__':
    unittest.main()
