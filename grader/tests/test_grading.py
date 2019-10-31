from unittest import main, TestCase
from unittest.mock import patch
from importlib import reload

from tests.utils import Console
from lib.print import enter_quiet_mode
from lib.grade import record_result, grade
import self as grader


class TestGrading(TestCase):

    def setUp(self):
        self.grade = ''

    def save_grade(self, grade):
        self.grade = grade

    @patch('lib.grade.print_grade')
    def test_mandatory_property(self, mock):
        mock.side_effect = self.save_grade

        enter_quiet_mode()

        record_result(True, '', '', '')
        grade()

        self.assertEqual(
            self.grade, 2, 'if all tests are passed, the grade should be 2')

        record_result(False, '', '', '', should_succeed=False)
        grade()

        self.assertEqual(
            self.grade, 5, 'no positive grade without passing one positive test')

        record_result(False, '', '', '', should_succeed=False)
        record_result(True, '', '', '', should_succeed=True)
        grade()

        self.assertEqual(
            self.grade, 2, 'postive grade with at least one positive test')

        record_result(True, '', '', '', should_succeed=True)
        record_result(True, '', '', '', should_succeed=True)
        record_result(True, '', '', '', should_succeed=True)
        record_result(True, '', '', '', should_succeed=True)
        record_result(False, '', '', '', should_succeed=True, mandatory=True)
        grade()

        self.assertEqual(
            self.grade, 5, 'can not pass when failing a mandatory test')

    def print_grade(self, grade):
        self.assertEqual(grade, 5, msg='{} has to fail for default Selfie'.format(
            self.current_assignment))

    @patch('lib.grade.print_grade')
    def test_default_grade(self, mock):
        assignments = list(
            map(lambda t: grader.name(t), grader.assignments[1:]))

        mock.side_effect = self.print_grade

        for assignment in assignments:
            self.current_assignment = assignment

            grader.main(['grader/self.py', '-q', assignment])


if __name__ == '__main__':
    main()
