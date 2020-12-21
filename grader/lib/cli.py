import os
import re
import sys
from argparse import ArgumentParser, RawDescriptionHelpFormatter, ArgumentTypeError
from io import StringIO
from pathlib import Path
from subprocess import run, DEVNULL
from typing import Callable, Optional, List, Tuple, Dict, Set

from lib.functional import flatmap
from lib.model import Assignment, Check, CheckResult
from lib.grade import grade
from lib.checks import set_home_path, set_assignment_name
from lib.print import (enter_quiet_mode, leave_quiet_mode, print_error,
                       print_message, print_warning, print_grade, print_processing,
                       stop_processing_spinner, print_passed, print_failed,
                       reset_truncate, set_truncate)

DEFAULT_BULK_GRADE_DIRECTORY = os.path.abspath('./.repositories')
GRADER_SYNOPSIS = '''
The Selfie Autograder is a tool that enables students and teachers evaluating
assignments that shall extend or adapt Selfie with concepts learned in lectures
on selfie. It also enables teachers bulk grading students' Git repositories.

The autograder is part of the Selfie Project of the Computational Systems Group
at the Department of Computer Sciences of the University of Salzburg in Austria,
http://selfie.cs.uni-salzburg.at

For more detailed information about its usage, please consult the README.
'''

bulk_grade_mode = False
file_with_commit_links = None
bulk_grade_directory = DEFAULT_BULK_GRADE_DIRECTORY


def error(msg):
    print_error(msg)
    exit(1)

def list_assignments_str(assignments: List[Assignment]) -> str:
    def print_assignment_of_lecture(lecture, stream):
        print(lecture + ' Assignments:', file=stream)

        for assignment in filter(lambda x: x.lecture is lecture, assignments):
            print('  {}'.format(assignment.name), file=stream)

        print(file=stream)

    stream = StringIO()

    print_assignment_of_lecture('General', stream)
    print_assignment_of_lecture('Compiler', stream)
    print_assignment_of_lecture('Systems', stream)

    return stream.getvalue()


def parse_assignment(args: str, assignments: Set[Assignment]) -> Optional[Assignment]:
    if not args:
        return None

    possible_assignment = list(filter(lambda a: a.name == args, assignments))

    if len(possible_assignment) == 1:
        return possible_assignment[0]

    error('unknown test: {}'.format(args))

def parse_truncate_range(arg: str) -> int:
    try:
        value = int(arg)

        if value < 0:
            raise ArgumentTypeError("truncate line count must be a natural number")

        return value
    except ValueError:
        raise ArgumentTypeError("truncate line count must be an integer")


def validate_options_for(assignment: Optional[Assignment]):
    if not bulk_grade_mode and assignment is None:
        error('please specify an assignment')


def execute_with_output(check: Check) -> CheckResult:
    print_processing(check.msg)

    try:
        result = check.execute()
    finally:
        stop_processing_spinner()

    if result.result == result.should_succeed:
        print_passed(check.msg)
    else:
        print_failed(check.msg, result.warning, result.output, result.command)

    return result


def check_assignment(assignment: Assignment, baseline: Assignment) -> Tuple[int, List[str]]:
    def check(a: Assignment):
        return list(map(execute_with_output, a.create_checks()))

    def change_result_to_mandatory(r: CheckResult):
        return CheckResult(r.result, r.msg, r.output, r.warning, r.should_succeed, r.command, True)

    if assignment != baseline:
        baseline_results = list(map(change_result_to_mandatory, check(baseline)))
    else:
        baseline_results = [ ]

    set_assignment_name(assignment.category)

    print_message('executing test \'{}\''.format(assignment.name))

    results = baseline_results + check(assignment)

    set_assignment_name('')

    (grade_value, reasons) = grade(results)

    for reason in reasons:
        print_warning(reason)

    print_grade(grade_value)


def enable_bulk_grader(file):
    global bulk_grade_mode, file_with_commit_links

    if not os.path.exists(file):
        error('the file "' + file + '" does not exist')

    if not os.path.isfile(file):
        error('the path "' + file + '" is not a file')

    bulk_grade_mode = True
    file_with_commit_links = os.path.abspath(file)


def set_bulk_grade_directory(directory):
    global bulk_grade_directory

    bulk_grade_directory = os.path.abspath(directory)


def parse_commit_url(url) -> Optional[Dict]:
    matcher = re.match(
        '^https://github.com/([^/]+)/([^/]+)/commit/([0-9a-f]+)$', url)

    if matcher is None:
        return None
    else:
        return {
            'user': matcher.group(1),
            'repo': matcher.group(2),
            'commit': matcher.group(3)
        }


def do_bulk_grading(assignment: Optional[Assignment], base_test: Assignment):
    if not os.path.exists(bulk_grade_directory):
        os.mkdir(bulk_grade_directory)

    working_directory = os.getcwd()

    os.chdir(bulk_grade_directory)

    with open(file_with_commit_links, 'rt') as file:
        for line in file.readlines():
            info = parse_commit_url(line)

            if info is None:
                print_message(line + '" is not a valid github commit link')
                continue

            repo_id = '{}/{}'.format(info['user'], info['repo'])

            print_message(repo_id + ': ', end='', loud=True)

            clone_dir = os.path.join(bulk_grade_directory, repo_id)

            if not os.path.exists(clone_dir):
                status = run(
                        ['git', 'clone', '-q', 'git@github.com:{}'.format(repo_id), repo_id],
                        stdout=DEVNULL, stderr=DEVNULL).returncode

                if status != 0:
                    print_message('error while cloning ' + repo_id, loud=True)
                    continue

            os.chdir(clone_dir)

            # remove all changes in local repository
            run(['git', 'reset', '--hard', '-q'], stdout=DEVNULL, stderr=DEVNULL)

            # fetch updates from github repository
            run(['git', 'fetch', '-q'], stdout=DEVNULL, stderr=DEVNULL)

            # change the local repository state using the commit ID
            status = run(
                    ['git', 'checkout', '-q', info['commit']],
                    stdout=DEVNULL, stderr=DEVNULL).returncode

            if status == 0:
                if assignment is None:
                    print_message('updated', loud=True)
                else:
                    print_message('')
                    check_assignment(assignment, base_test)
                    print_message('', loud=True)
            else:
                print_message(
                    'commit hash "{}" is not valid'.format(info['commit']))

            os.chdir(bulk_grade_directory)

    os.chdir(working_directory)

    if bulk_grade_directory is DEFAULT_BULK_GRADE_DIRECTORY:
        os.system('rm -rf {}'.format(bulk_grade_directory))


def reset_state():
    global bulk_grade_mode, bulk_grade_directory
    global file_with_commit_links

    bulk_grade_mode = False
    file_with_commit_links = None
    bulk_grade_directory = DEFAULT_BULK_GRADE_DIRECTORY
    set_assignment_name('')

    leave_quiet_mode()
    reset_truncate()


def process_arguments(argv: List[str], assignments: Set[Assignment], baseline: Assignment):
    def curried_parse_assignment(assignment: str) -> Optional[Assignment]:
        return parse_assignment(assignment, assignments)

    parser = ArgumentParser(argv[0], formatter_class=RawDescriptionHelpFormatter,
            description=GRADER_SYNOPSIS, epilog=list_assignments_str(assignments))

    parser.add_argument('-q', action='store_true', default=False,
            help='print grade only', dest='quiet')
    parser.add_argument('-b', default=None, metavar="<file>",
            help='bulk grade assignments given as github commit links in file',
            dest='bulk_file')
    parser.add_argument('-d', default=None, metavar="<directory>",
            help='directory where all bulk-graded repositories are stored',
            dest='bulk_directory')
    parser.add_argument('--truncate', metavar=('trailing', 'leading'), nargs=2,
            type=parse_truncate_range,
            help='truncates the amount of leading and trailing lines',
            dest='truncate')
    parser.add_argument('assignment', metavar='assignment', nargs='?',
            type=curried_parse_assignment, help='grade this assignment')

    try:
        if len(argv) <= 1:
            parser.print_help()
            exit()

        set_home_path(Path(os.path.abspath(os.path.dirname(argv[0]))))

        args = parser.parse_args(argv[1:])

        if args.quiet:
            enter_quiet_mode()

        if args.truncate:
            set_truncate(*args.truncate)

        if args.bulk_file:
            enable_bulk_grader(args.bulk_file)

        if args.bulk_directory:
            set_bulk_grade_directory(args.bulk_directory)

        validate_options_for(args.assignment)

        if bulk_grade_mode:
            do_bulk_grading(args.assignment, baseline)
        else:
            check_assignment(args.assignment, baseline)

    finally:
        reset_state()
