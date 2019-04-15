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

  @classmethod
  def setUpClass(self):
    system('rm -rf grader/tests/.build && mkdir grader/tests/.build >/dev/null 2>&1')
    system('python3 grader/tools/clone-from-links.py grader/tests/links.txt grader/tests/.build >/dev/null 2>&1')

  @classmethod
  def tearDownClass(self):
    system('rm -rf grader/tests/.build')

  def test_bulk_cloning(self):
    self.assertTrue(isfile('grader/tests/.build/ChristianMoesl/selfie/selfie.c'))
    self.assertTrue(isfile('grader/tests/.build/cksystemsteaching/selfie/selfie.c'))

  def test_bulk_grading(self):
    # Modify user grader
    system('rm -rf grader/tests/.build/ChristianMoesl/selfie/grader')
    system('rm -rf grader/tests/.build/cksystemsteaching/selfie/grader')

    self.assertFalse(isfile('grader/tests/.build/ChristianMoesl/selfie/grader/self.py'))
    self.assertFalse(isfile('grader/tests/.build/cksystemsteaching/selfie/grader/self.py'))

    process = Popen('python3 grader/tools/grade-from-links.py grader/tests/links.txt ../../../../.. grader/tests/.build base', stdout=PIPE, stderr=PIPE, shell=True)
    output = process.communicate()[0].decode(sys.stdout.encoding)

    self.assertEqual(process.returncode, 0)

    for line in output.split('\n'):
      self.assertTrue(line == '' or re.match('[^/]+/[^/:]+: [1-5]', line) != None)

if __name__ == '__main__':
  unittest.main()