import os
import sys
import unittest
from importlib import reload
from shutil import copyfile
from unittest.mock import patch
from typing import Callable, Optional, List, Set, Tuple, Any

from tests.utils import (CaptureOutput, assemble_for_selfie,
                         for_all_test_results, list_files)

import self as grader
from lib.checks import execute
from lib.model import Assignment, Check, CheckResult
from self import baseline_assignments, main


class TestCli(unittest.TestCase):

    def setUp(self):
        self.assignments = grader.assignments
        self.baseline_assignments = grader.baseline_assignments

        grader.baseline_assignments = [
            # capture index in closure with python default value of lambda
            Assignment(a.name, a.lecture, a.category, a.description, lambda i=i: self.check_baseline_assignment_mock(i))
            for i, a in enumerate(grader.baseline_assignments)
        ]

        grader.assignments = [
            Assignment(a.name, a.lecture, a.category, a.description, self.check_assignment_mock)
            for a in grader.assignments
        ]

        self.count = 0

    def tearDown(self):
        grader.assignments = self.assignments
        grader.baseline_assignments = self.baseline_assignments

    def check_baseline_assignment_mock(self, n_th_baseline) -> List[Check]:
        def assert_order(i) -> CheckResult:
            self.assertEqual(self.count, i)
            self.count = self.count + 1

            return CheckResult(True, '', '', '')

        return [Check('', '', lambda: assert_order(n_th_baseline))]

    def check_assignment_mock(self) -> List[Check]:
        def assert_executed_after_baseline() -> CheckResult:
            self.assertEqual(self.count, len(self.baseline_assignments))

            return CheckResult(True, '', '', '')

        return [Check('', '', assert_executed_after_baseline)]

    def test_baseline_execution_order(self):
        with CaptureOutput():
            grader.main([sys.argv[0], list(self.assignments)[0].name])


if __name__ == '__main__':
    unittest.main()
