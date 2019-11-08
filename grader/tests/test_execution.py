import sys
from unittest import TestCase, main
from unittest.mock import patch

from lib.system import EXITCODE_ERROR_RANGE
from lib.output_processing import filter_status_messages
from tests.utils import (Console, compile_with_gcc_and_run,
                              run_compilable_assignments)
from self import directory, main as grader_main

class TestExecution(TestCase):

    def save_directory(self, assignment):
        self.assignment = directory(assignment)

    def execution_mock(self, file, success_criteria, msg):

        if 'invalid' not in file:
            return_value, out, err = compile_with_gcc_and_run(
                'assignments/' + self.assignment + '/' + file)

            msg = 'compiling ' + file + ' with gcc and running the programming gives the expected result'

            if type(success_criteria) is int:
                self.assertNotIn(success_criteria, EXITCODE_ERROR_RANGE,
                                'The hypster execution result value can also be an Selfie error code')

                self.assertEqual(success_criteria, return_value, msg)

            elif type(success_criteria) is str:
                filtered = filter_status_messages(out)

                self.assertIs(filtered, success_criteria, msg)

            elif callable(success_criteria):
                self.assertTrue(success_criteria(return_value, out)[0], msg)
            else:
                self.assertTrue(False)


    @patch('self.test_mipster_execution')
    def test_mipster_execution_results(self, test_mipster_execution_mock):
        test_mipster_execution_mock.side_effect = self.execution_mock

        run_compilable_assignments(self.save_directory)


    @patch('self.test_hypster_execution')
    def test_hypster_execution_results(self, test_hypster_execution_mock):
        test_hypster_execution_mock.side_effect = self.execution_mock

        run_compilable_assignments(self.save_directory)


if __name__ == '__main__':
    main()
