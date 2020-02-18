import os
import re
import sys
from pathlib import Path
from subprocess import run
from typing import Callable, Optional, List, Tuple, Dict, Set

from lib.functional import flatmap
from lib.model import Assignment, Check, CheckResult
from lib.grade import grade
from lib.checks import set_home_path, set_assignment_name
from lib.print import (is_in_quiet_mode, enter_quiet_mode, leave_quiet_mode, print_error,
                       print_message, print_usage, print_warning, print_grade, print_processing,
                       stop_processing_spinner, print_passed, print_failed)

DEFAULT_BULK_GRADE_DIRECTORY = os.path.abspath('./.repositories')

bulk_grade_mode = False
file_with_commit_links = None
bulk_grade_directory = DEFAULT_BULK_GRADE_DIRECTORY


def error(msg):
    print_error(msg)
    exit(1)


def parse_options(args, option_flags):
    i = 0

    options = list(map(lambda x: x[0], option_flags))

    while len(args) > i and args[i][0] == '-':
        if args[i] in options:
            index = options.index(args[i])

            if option_flags[index][2] is None:
                option_flags[index][1]()
            else:
                i += 1

                if len(args) > i:
                    option_flags[index][1](args[i])
                else:
                    error('option flag "' + option_flags[index][0] +
                          '" needs an argument ' + option_flags[index][2])
        else:
            error('unknown option: ' + args[i])

        i += 1

    return args[i:]


def parse_assignment(args: List[str], assignments: Set[Assignment]) -> Optional[Assignment]:
    if len(args) == 0:
        return None

    if len(args) > 1:
        error('only 1 assignment allowed')

    possible_assignment = list(filter(lambda a: a.name == args[0], assignments))

    if len(possible_assignment) == 1:
        return possible_assignment[0]

    error('unknown test: {}'.format(args))


def validate_options_for(assignment: Optional[Assignment]):
    if not bulk_grade_mode and is_in_quiet_mode() and assignment is None:
        error('please specify a assignment')


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
                status = os.system(
                    'git clone -q git@github.com:{} {} >/dev/null 2>&1'.format(repo_id, repo_id))

                if status != 0:
                    print_message('error when cloning ' + repo_id, loud=True)
                    continue

            os.chdir(clone_dir)

            # remove all changes in local repository
            os.system('git reset --hard -q >/dev/null 2>&1')

            # fetch updates from github repository
            os.system('git fetch -q >/dev/null 2>&1')

            # change the local repository state using the commit ID
            status = os.system(
                'git checkout -q {} >/dev/null 2>&1'.format(info['commit']))

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


print_usage_flag = False


def set_print_usage():
    global print_usage_flag
    print_usage_flag = True


option_flags = [
    ('-q', enter_quiet_mode, None, 'only the grade is printed'),
    ('-h', set_print_usage, None, 'this help text'),
    ('-b', enable_bulk_grader, '<file>',
     'bulk grade assignments defined by a file with github commit links'),
    ('-d', set_bulk_grade_directory, '<directory>',
     'path where all bulk graded repositories should be saved')
]


def reset_state():
    global bulk_grade_mode, bulk_grade_directory
    global file_with_commit_links
    global print_usage_flag

    bulk_grade_mode = False
    file_with_commit_links = None
    bulk_grade_directory = DEFAULT_BULK_GRADE_DIRECTORY
    set_assignment_name('')
    print_usage_flag = False

    leave_quiet_mode()


def process_arguments(argv: List[str], assignments: Set[Assignment], baseline: Assignment):
    try:
        if len(argv) <= 1:
            print_usage(option_flags, assignments)
            exit()

        set_home_path(Path(os.path.abspath(os.path.dirname(argv[0]))))

        args = parse_options(argv[1:], option_flags)

        assignment = parse_assignment(args, assignments)

        validate_options_for(assignment)

        if print_usage_flag:
            print_usage(option_flags, assignments)
            exit()

        if bulk_grade_mode:
            do_bulk_grading(assignment, baseline)
        else:
            check_assignment(assignment, baseline)

    finally:
        reset_state()
