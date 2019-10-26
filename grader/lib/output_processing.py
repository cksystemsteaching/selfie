import re
import sys

sys.setrecursionlimit(5000)

STATUSMESSSAGE_START = r'([a-zA-Z]:\\|(./)?selfie)'

def contains_name(output):
    result = re.match(STATUSMESSSAGE_START + r'[^\n]*This is \S* \S* Selfie[^\n]*\n', output) != None

    return (result, 'The selfie output does not contain "This is <firstname> <secondname>\'s Selfie')

def filter_status_messages(output):
    return re.sub(STATUSMESSSAGE_START + r'[^\n]*\n', '', output).replace('\n', '')


class Memoize:
    def __init__(self, fn):
        self.fn = fn
        self.memo = {}

    def __call__(self, *args):
        h = len(args[1]) + sum([i * 100 * x for i,
                                x in enumerate(map(lambda s: len(s), args[0]), 1000)])
        if h not in self.memo:
            self.memo[h] = self.fn(*args)
        return self.memo[h]


@Memoize
def is_interleaved(strings, interleaved):
    if all(len(string) == 0 for string in strings) and len(interleaved) == 0:
        return True

    if len(interleaved) == 0:
        return False

    for i, string in enumerate(filter(lambda s: len(s) > 0, strings)):
        tmp = strings.copy()
        tmp[i] = tmp[i][1:]
        if interleaved[0] == string[0] and is_interleaved(tmp, interleaved[1:]):
            return True

    return False


def is_interleaved_output(output, interleaved_msg, number_of_interleaved):
    strings = [interleaved_msg[:] for i in range(0, number_of_interleaved)]

    filtered_output = filter_status_messages(output)

    if filtered_output == interleaved_msg * number_of_interleaved:
        return (False, 'The output strings are ordered sequentially')
    else:
        return (is_interleaved(strings, filtered_output), 'The output strings are not interleaved')


def is_permutation_of(output, numbers):
    filtered_output = filter_status_messages(output)

    printed_numbers = list(map(lambda x: int(x), filter(
        lambda s: len(s) > 0 and s.isdigit(), filtered_output.split(' '))))

    if (len(printed_numbers) != len(numbers)):
        return (False, 'The amount of printed numbers ({}) is not equal to the amount of numbers needed to be printed ({})'.format(len(printed_numbers), len(numbers)))

    for number in numbers:
        if number in printed_numbers:
            printed_numbers.remove(number)
        else:
            return (False, 'The printed numbers are not a permutation of {}'.format(numbers))

    return (len(printed_numbers) == 0, 'The printed numbers are not a permutation of {}'.format(numbers))


def has_compiled(returncode, output):
    match = re.search('(syntax error [^\n]*)', output)

    if match != None:
        return (False, match.group(0))
    elif returncode != 0:
        return (False, 'compiler returned status {}'.format(returncode))

    return (True, None)


def has_no_compile_warnings(return_value, output):
    if return_value != 0:
        warning = 'selfie terminates with an error code of {} during self-compilation'.format(
            return_value)
        succeeded = False
    else:
        syntax_error_matcher = re.search('(syntax error [^\n]*)', output)
        type_warning_matcher = re.search('(warning [^\n]*)', output)

        if syntax_error_matcher != None:
            warning = syntax_error_matcher.group(0)
            succeeded = False
        elif type_warning_matcher != None:
            warning = type_warning_matcher.group(0)
            succeeded = False
        else:
            warning = None
            succeeded = True

    return (succeeded, warning)

