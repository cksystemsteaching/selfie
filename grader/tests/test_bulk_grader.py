import unittest
import sys
import re
from os import system
from os.path import isfile
from subprocess import Popen, PIPE

from grader.tests.lib import Console, compile_with_gcc_and_run
from grader.self import main, defined_tests
import grader.self

class TestBulkGrader(unittest.TestCase):

  def test_bulk_grading_with_wrong_arguments(self):
    process = Popen('grader/self.py -b', stdout=PIPE, stderr=PIPE, shell=True)
    process.communicate()
    self.assertNotEqual(process.returncode, 0)

    process = Popen('grader/self.py -d', stdout=PIPE, stderr=PIPE, shell=True)
    process.communicate()
    self.assertNotEqual(process.returncode, 0)

  def test_bulk_grading(self):
    process = Popen('grader/self.py -b grader/tests/links.txt base', stdout=PIPE, stderr=PIPE, shell=True)
    output = process.communicate()[0].decode(sys.stdout.encoding)

    self.assertEqual(process.returncode, 0)

    for line in output.split('\n'):
      self.assertTrue(line == '' or re.match('[^/]+/[^/:]+: [1-5]', line) != None)

if __name__ == '__main__':
  unittest.main()