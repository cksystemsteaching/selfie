import os
import re
import sys
from lib.print import print_usage, print_loud, enter_quiet_mode, leave_quiet_mode
from lib.grade import grade

DEFAULT_BULK_GRADE_DIRECTORY = os.path.abspath('./.repositories')

bulk_grade_mode = False
file_with_commit_links = None
bulk_grade_directory = DEFAULT_BULK_GRADE_DIRECTORY
assignment_path = ''


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
                    print('option flag "' + option_flags[index][0] +
                          '" needs an argument ' + option_flags[index][2])
                    exit(1)
        else:
            print('unknown option: ' + args[i])
            exit(1)

        i += 1

    return args[i:]


def parse_assignment(args, assignments):
    assignment_names = list(map(lambda x: x[0], assignments))

    if len(args) == 0:
        return None

    if len(args) > 1:
        print('only 1 assignment allowed')
        exit(1)

    if args[0] in assignment_names:
        return assignments[assignment_names.index(args[0])]

    print('unknown test: {}'.format(args))
    exit(1)


def validate_options_for(assignment):
    if bulk_grade_mode and assignment == '':
        print('please specify a test used for bulk grading')
    else:
        return

    exit(1)


def check_assignment(assignment, base_test):
    global assignment_path

    if assignment[3] != base_test:
        base_test(mandatory=True)

    assignment_path = assignment[2]

    print('executing test \'{}\''.format(assignment[0]))

    assignment[3]()

    assignment_path = ''

    grade()


def enable_bulk_grader(file):
    global bulk_grade_mode, file_with_commit_links

    if not os.path.exists(file):
        print('the file "' + file + '" does not exist')
        exit(1)

    if not os.path.isfile(file):
        print('the path "' + file + '" is not a file')
        exit(1)

    bulk_grade_mode = True
    file_with_commit_links = os.path.abspath(file)


def set_bulk_grade_directory(directory):
    global bulk_grade_directory

    bulk_grade_directory = os.path.abspath(directory)


def do_bulk_grading(assignment, base_test):
    enter_quiet_mode()

    if not os.path.exists(bulk_grade_directory):
        os.mkdir(bulk_grade_directory)

    working_directory = os.getcwd()

    os.chdir(bulk_grade_directory)

    with open(file_with_commit_links, 'rt') as file:
        for line in file.readlines():
            matcher = re.match(
                '^https://github.com/([^/]+)/([^/]+)/commit/([0-9a-f]+)$', line)

            if matcher is None:
                print('the link "' + line + '" is not a valid github commit link')
                exit(1)

            user = matcher.group(1)
            repo = matcher.group(2)
            commit = matcher.group(3)

            clone_dir = os.path.join(
                bulk_grade_directory, '{}/{}'.format(user, repo))

            if not os.path.exists(clone_dir):
                os.system(
                    'git clone -q https://github.com/{}/{} {}/{}'.format(user, repo, user, repo))

            os.chdir(clone_dir)

            # remove all changes in local repository
            os.system('git reset --hard -q')

            # fetch updates from github repository
            os.system('git fetch -q')

            # change the local repository state using the commit ID
            os.system('git checkout -q {}'.format(commit))

            print_loud('{}/{}: '.format(user, repo), end='')
            check_assignment(assignment, base_test)
            print_loud('')

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


def process_arguments(argv, assignments):
    try:
        if len(argv) <= 1:
            print_usage(option_flags, assignments)
            exit()

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
        leave_quiet_mode()
