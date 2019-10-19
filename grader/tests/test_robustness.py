from unittest import TestCase, main
from os import chdir, getcwd
from shutil import copytree, rmtree
from unittest.mock import patch

from grader.tests.lib import Console
from grader.self import main as grader_main, execute, EXITCODE_IOERROR
import grader.self

original_execute = execute


def ignore(root, paths):
    if './grader/tests/.tmp' in root:
        return paths

    return []


class TestRobustness(TestCase):

    def setUp(self):
        patcher = patch('grader.self.print_loud')
        self.addCleanup(patcher.stop)
        self.mock_foo = patcher.start()

        rmtree('/tmp/sel fie', ignore_errors=True)

    def execute_mock(self, command):
        ret_code, output, error_output = original_execute(command)

        self.assertNotEqual(ret_code, EXITCODE_IOERROR)

        return (ret_code, output, error_output)

    @patch('grader.self.execute')
    def test_path_name_with_whitespaces(self, mock):
        mock.side_effect = lambda c: self.execute_mock(c)

        dst = '/tmp/sel fie'

        copytree('.', dst, ignore=ignore)

        cwd = getcwd()

        chdir('/tmp/sel fie')

        with Console():
            grader_main([getcwd(), 'hex-literal'])

        chdir(cwd)

        rmtree(dst)


if __name__ == '__main__':
    main()
