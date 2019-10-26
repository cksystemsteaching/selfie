import unittest
from unittest.mock import patch
import sys
import os
from importlib import reload
from shutil import copyfile

from self import main, name, assignments
from lib.runner import execute  
from tests.utils import assemble_for_selfie, Console, for_all_test_results, list_files

import self as grader


class TestRiscvInstruction(unittest.TestCase):

    def setUp(self):
        patcher = patch('lib.grade.print_loud')
        self.addCleanup(patcher.stop)
        self.mock_foo = patcher.start()

    @classmethod
    def setUpClass(self):
        self.instructions = list(
            map(lambda f: f[:-2], list_files('tests/instructions', extension='.s')))

    def execute_mock(self, command):
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
                result, 'following encoding test passed: "' + msg + '"')
        if 'assembly instruction format' in msg:
            self.assertTrue(
                result, 'following format test passed: "' + msg + '"')

    @patch('lib.runner.execute')
    def test_instruction(self, mock):
        mock.side_effect = self.execute_mock

        output = ''

        for assignment in assignments:
            with Console() as console:
                grader.main([sys.argv[0], name(assignment)])

                output = output + console.get_output()

            reload(grader)

        for_all_test_results(output, self.check_encoding_results)


if __name__ == '__main__':
    unittest.main()
