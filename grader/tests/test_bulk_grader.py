import unittest
import sys
import re
import os
import subprocess
# from os import system
from os.path import isfile
import shlex
from subprocess import Popen, PIPE, run
from unittest.mock import patch

from self import main as grader_main
from lib.print import println
from tests.utils import CaptureOutput, compile_with_gcc_and_run


class ExitError(Exception):
    def __init__(self, code):
        self.message = str(code)


class TestBulkGrader(unittest.TestCase):

    def commit_without_auth(self, command, **kwargs):
        return run([arg.replace('git@github.com:', 'https://github.com/') for arg in command], **kwargs)

    @patch('lib.cli.run') # imported from subprocess
    def test_bulk_grading_with_wrong_arguments(self, mock):
        mock.side_effect = self.commit_without_auth

        process = Popen(shlex.split('./self.py -b'), stdout=PIPE,
                        stderr=PIPE)
        process.communicate()
        self.assertNotEqual(process.returncode, 0)

        process = Popen(shlex.split('./self.py -d'), stdout=PIPE,
                        stderr=PIPE)
        process.communicate()
        self.assertNotEqual(process.returncode, 0)

    def exit_mock(self, code):
        if code != 0:
            raise ExitError(code)

    @patch('lib.cli.exit')
    @patch('lib.cli.run') # imported from subprocess
    def test_bulk_grading(self, mock, exit_mock):
        mock.side_effect = self.commit_without_auth

        exit_mock.side_effect = self.exit_mock

        with CaptureOutput() as capture:
            grader_main([sys.argv[0], '-b', 'tests/links.txt', 'self-compile'])

            output = capture.get_loud_output()

        for line in output.split('\n'):
            self.assertTrue(line == '' or re.match(
                '[^/]+/[^/:]+: [1-5]', line) != None)

    def test_cloning_without_permissions(self):
        with CaptureOutput() as capture:
            grader_main([sys.argv[0], '-b', 'tests/links.txt', 'self-compile'])

            output = capture.get_loud_output()

        # should not raise an exception and state errors for both repositories
        self.assertIn('cksystemsteaching/selfie: ', output)
        self.assertIn('ChristianMoesl/selfie: ', output)


if __name__ == '__main__':
    unittest.main()
