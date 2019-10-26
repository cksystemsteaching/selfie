import unittest
from unittest.mock import patch
import sys
import os

from self import main, assignments, name, test, directory
from tests.utils import Console, compile_with_gcc, run_compilable_assignments

class TestCompilable(unittest.TestCase):

    def setUp(self):
        patcher = patch('lib.grade.print_loud')
        self.addCleanup(patcher.stop)
        self.mock_foo = patcher.start()

    def is_compilable(self, file):
        return not ('invalid' in file or 'missing' in file)

    def compilable_mock(self, file, msg, should_succeed=True):
        file_path = 'assignments/' + self.assignment + '/' + file

        is_compilable = self.is_compilable(file)

        self.assertEqual(is_compilable, should_succeed)

        if not is_compilable:
            self.assertNotEqual(compile_with_gcc(
                file_path), 0, 'compiling ' + file + ' with gcc leads to an error')
        else:
            self.assertEqual(compile_with_gcc(file_path), 0,
                             'compiling ' + file + ' with gcc leads to no error')

    def save_assignment(self, assignment):
        self.assignment = directory(assignment)

    @patch('self.test_compilable')
    def test_compilability_of_test_files(self, test_compilable_mock):

        test_compilable_mock.side_effect = self.compilable_mock

        run_compilable_assignments(self.save_assignment)


if __name__ == '__main__':
    unittest.main()
