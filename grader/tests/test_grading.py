from unittest import main, TestCase
from unittest.mock import patch
from importlib import reload

import grader.self as grader


class TestGrading(TestCase):

  def print_loud(self, msg, end='\n'):
    self.assertEqual(int(msg), 5, msg='{} has to fail for default Selfie'.format(self.current_assignment))

  def test_default_grade(self):
    assignments = list(map(lambda t: t[0], grader.defined_tests))
    assignments.remove('base')

    for assignment in assignments:
      self.current_assignment = assignment

      with patch('grader.self.print_loud') as mock:
        mock.side_effect = self.print_loud
        grader.main(['grader/self.py', '-q', assignment])

      reload(grader)


if __name__ == '__main__':
  main()
