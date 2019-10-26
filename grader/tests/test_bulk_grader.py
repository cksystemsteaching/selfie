import unittest
import sys
import re
from os import system
from os.path import isfile
import shlex
from subprocess import Popen, PIPE

from self import main
from tests.utils import Console, compile_with_gcc_and_run

class TestBulkGrader(unittest.TestCase):

    def test_bulk_grading_with_wrong_arguments(self):
        process = Popen(shlex.split('./self.py -b'), stdout=PIPE,
                        stderr=PIPE)
        process.communicate()
        self.assertNotEqual(process.returncode, 0)

        process = Popen(shlex.split('./self.py -d'), stdout=PIPE,
                        stderr=PIPE)
        process.communicate()
        self.assertNotEqual(process.returncode, 0)

    def test_bulk_grading(self):
        process = Popen(shlex.split('./self.py -b tests/links.txt self-compile'),
                        stdout=PIPE, stderr=PIPE)
        output = process.communicate()[0].decode(sys.stdout.encoding)

        self.assertEqual(process.returncode, 0)

        for line in output.split('\n'):
            self.assertTrue(line == '' or re.match(
                '[^/]+/[^/:]+: [1-5]', line) != None)


if __name__ == '__main__':
    unittest.main()

