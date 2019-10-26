import sys
from unittest import TestCase, main
from unittest.mock import patch

from lib.system import EXITCODE_ERROR_RANGE
from tests.utils import (Console, compile_with_gcc_and_run,
                              run_compilable_assignments)
from self import directory, main as grader_main

class TestMipsterExecution(TestCase):

    def setUp(self):
        patcher = patch('lib.grade.print_loud')
        self.addCleanup(patcher.stop)
        self.mock_foo = patcher.start()

    def mipster_execution_mock(self, file, result, msg):
        self.assertNotIn(result, EXITCODE_ERROR_RANGE,
                         'The mipster execution result value can also be an Selfie error code')

        if 'invalid' not in file:
            return_value = compile_with_gcc_and_run(
                'assignments/' + self.assignment + '/' + file)

            self.assertEqual(result, return_value, 'compiling ' + file +
                             ' with gcc and running the programming gives the expected result')

    def save_directory(self, assignment):
        self.assignment = directory(assignment)

    @patch('self.test_mipster_execution')
    def test_mipster_execution_results(self, test_mipster_execution_mock):
        test_mipster_execution_mock.side_effect = self.mipster_execution_mock

        run_compilable_assignments(self.save_directory)

    def hypster_execution_mock(self, file, result, msg):
        self.assertNotIn(result, EXITCODE_ERROR_RANGE,
                         'The hypster execution result value can also be an Selfie error code')

        if 'invalid' not in file:
            return_value = compile_with_gcc_and_run(
                'assignments/' + self.assignment + '/' + file)

            self.assertEqual(result, return_value, 'compiling ' + file +
                             ' with gcc and running the programming gives the expected result')

    @patch('self.test_hypster_execution')
    def test_hypster_execution_results(self, test_hypster_execution_mock):
        test_hypster_execution_mock.side_effect = self.hypster_execution_mock

        run_compilable_assignments(self.save_directory)


if __name__ == '__main__':
    main()
