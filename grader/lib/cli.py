import os
import re
import sys
from pathlib import Path
from subprocess import run

from lib.grade import grade
from lib.runner import set_home_path, set_assignment_name
from lib.print import (is_in_quiet_mode, enter_quiet_mode, leave_quiet_mode, print_error,
                       print_message, print_usage)

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


def parse_assignment(args, assignments):
    assignment_names = list(map(lambda x: x[0], assignments))

    if len(args) == 0:
        return None

    if len(args) > 1:
        error('only 1 assignment allowed')

    if args[0] in assignment_names:
        return assignments[assignment_names.index(args[0])]

    error('unknown test: {}'.format(args))


def validate_options_for(assignment):
    if not bulk_grade_mode and is_in_quiet_mode() and assignment is None:
        error('please specify a assignment')


def check_assignment(assignment, base_test):
    if assignment[3] != base_test:
        base_test(mandatory=True)

    set_assignment_name(assignment[2])

    print_message('executing test \'{}\''.format(assignment[0]))

    assignment[3]()

    set_assignment_name('')

    grade()


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


def parse_commit_url(url):
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


def do_bulk_grading(assignment, base_test):
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


def process_arguments(argv, assignments):
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

        base_test = assignments[0][3]

        if bulk_grade_mode:
            do_bulk_grading(assignment, base_test)
        else:
            check_assignment(assignment, base_test)

    finally:
        reset_state()
