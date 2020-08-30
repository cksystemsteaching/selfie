import unittest
from unittest.mock import patch
import sys
import os
from typing import List

from self import main, assignments
from lib.model import Check, CheckResult
from tests.utils import compile_with_gcc, run_compilable_assignments

class TestCompilable(unittest.TestCase):

    def is_compilable(self, file):
        return not ('invalid' in file or 'missing' in file)

    def compilable_mock(self, file, msg, should_succeed=True) -> List[Check]:
        def execute() -> CheckResult:
            file_path = 'assignments/' + self.assignment + '/' + file

            is_compilable = self.is_compilable(file)

            self.assertEqual(is_compilable, should_succeed)

            if not is_compilable:
                self.assertNotEqual(compile_with_gcc(
                    file_path), 0, 'compiling ' + file + ' with gcc leads to an error')
            else:
                self.assertEqual(compile_with_gcc(file_path), 0,
                                 'compiling ' + file + ' with gcc leads to no error')
            return CheckResult(True, "unittest", "", "")

        return [Check("compilable_check_mock", execute)]

    def save_assignment(self, assignment):
        self.assignment = assignment.category

    @patch('self.check_compilable')
    def test_compilability_of_test_files(self, check_compilable_mock):
        check_compilable_mock.side_effect = self.compilable_mock

        run_compilable_assignments(self.save_assignment)


if __name__ == '__main__':
    unittest.main()
