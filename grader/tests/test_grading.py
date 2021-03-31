from unittest import main, TestCase
from unittest.mock import patch
from importlib import reload

from tests.utils import Console
from lib.print import enter_quiet_mode
from lib.grade import grade
from lib.model import CheckResult
import self as grader


class TestGrading(TestCase):

    def setUp(self):
        self.grade = ''

    def save_grade(self, grade):
        self.grade = grade

    def test_mandatory_property(self):
        (mark, reasons) = grade([
            CheckResult(True, '', '', '')
        ])

        self.assertEqual(
            mark, 2, 'if all tests are passed, the grade should be 2')

        (mark, reasons) = grade([
            CheckResult(False, '', '', '', should_succeed=False)
        ])

        self.assertEqual(
            mark, 5, 'no positive grade without passing one positive test')

        (mark, reasons) = grade([
            CheckResult(False, '', '', '', should_succeed=False),
            CheckResult(True, '', '', '', should_succeed=True)
        ])

        self.assertEqual(
            mark, 2, 'postive grade with at least one positive test')

        (mark, reasons) = grade([
            CheckResult(True, '', '', '', should_succeed=True),
            CheckResult(True, '', '', '', should_succeed=True),
            CheckResult(True, '', '', '', should_succeed=True),
            CheckResult(True, '', '', '', should_succeed=True),
            CheckResult(False, '', '', '', should_succeed=True, mandatory=True)
        ])

        self.assertEqual(
            mark, 5, 'can not pass when failing a mandatory test')

    def print_grade(self, grade):
        self.assertEqual(grade, 5, msg='{} has to fail for default Selfie'.format(
            self.current_assignment))

    @patch('lib.cli.print_grade')
    def test_default_grade(self, mock):
        assignments = map(lambda a: a.name, grader.assignments)

        mock.side_effect = self.print_grade

        for assignment in assignments:
            self.current_assignment = assignment

            grader.main(['grader/self.py', '-q', assignment])


if __name__ == '__main__':
    main()
