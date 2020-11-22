from typing import List, Tuple
from lib.model import CheckResult
from lib.print import (print_failed, print_grade, print_loud, print_passed,
                       print_warning, stop_processing_spinner)


def record_result(result, msg, output, warning, should_succeed=True, command=None, mandatory=False):
    print("blaaaaa")
    global results

    stop_processing_spinner()

    # results.append((result, should_succeed, mandatory))

    if result == should_succeed:
        print_passed(msg)
    else:
        print_failed(msg, command, output, warning)


def grade(results: List[CheckResult]) -> Tuple[int, List[str]]:
    if len(results) == 0:
        return

    mandatory_tests = list(filter(lambda x: x.mandatory, results))
    normal_tests = list(filter(lambda x: not x.mandatory, results))

    number_of_tests = len(results) - len(mandatory_tests)
    number_of_tests_passed = len(
        list(filter(lambda x: x.result == x.should_succeed, normal_tests)))
    number_of_positive_tests_passed = len(
        list(filter(lambda x: x.result and x.should_succeed, normal_tests)))

    failed_mandatory_test = any(
        filter(lambda x: x.result != x.should_succeed, mandatory_tests))

    if number_of_tests_passed == 0 and number_of_tests != 0:
        passed = 0.0
    elif number_of_tests_passed == 0 and number_of_tests == 0: # No tests or only mandatory tests
        passed = 1.0
    else:
        passed = number_of_tests_passed / float(number_of_tests)

    reasons = [ ]

    if failed_mandatory_test or (number_of_positive_tests_passed == 0 and number_of_tests != 0):
        if failed_mandatory_test:
            reasons.append('you have failed a mandatory test')
        if number_of_positive_tests_passed == 0 and number_of_tests != 0:
            reasons.append('you have not passed at least one positive test')

        grade = 5
    elif passed == 1.0:
        grade = 2
    elif passed >= 0.5:
        grade = 3
    elif passed > 0.0:
        grade = 4
    else:
        grade = 5

    return (grade, reasons)
