import os
import sys
import unittest
from importlib import reload
from shutil import copyfile
from unittest.mock import patch

from tests.utils import (CaptureOutput, assemble_for_selfie,
                         for_all_test_results, list_files)

import self as grader
from lib.checks import execute
from self import assignments, main


class TestRiscvInstruction(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        self.instructions = list(
            map(lambda f: f[:-2], list_files('tests/instructions', extension='.s')))

    def execute_mock(self, command, timeout=60):
        if '.tmp.bin' in command:
            for instruction in self.instructions:
                if instruction in command:
                    assemble_for_selfie('instructions/' + instruction + '.s')

        if '.tmp.s' in command:
            for instruction in self.instructions:
                if instruction in command:
                    copyfile('tests/instructions/' +
                             instruction + '.s', '.tmp.s')

        return (0, '', '')

    def check_encoding_results(self, result, msg):
        if 'RISC-V encoding' in msg:
            self.assertTrue(
                result, 'following encoding test passed "' + msg + '"')
        if 'assembly instruction format' in msg:
            self.assertTrue(
                result, 'following format test passed "' + msg + '"')

    @patch('lib.checks.execute')
    def test_instruction(self, mock):
        mock.side_effect = self.execute_mock

        with CaptureOutput() as capture:
            for assignment in assignments:
                grader.main([sys.argv[0], assignment.name])

        for_all_test_results(capture.get_output(), self.check_encoding_results)


if __name__ == '__main__':
    unittest.main()
