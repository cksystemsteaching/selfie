from lib.print import print_passed, print_failed, print_loud, stop_processing_spinner

results = [ ]


def reset_assignment_results():
    global results
    results = [ ]


def record_result(result, msg, output, warning, should_succeed=True, command=None, mandatory=False):
    global results

    stop_processing_spinner()
   
    results.append((result, should_succeed, mandatory))
    
    if result == should_succeed:
        print_passed(msg)
    else:
        print_failed(msg, command, output, warning)


def grade(): 
    global results

    if len(results) == 0:
        return

    mandatory_tests = list(filter(lambda x: x[2], results))
    normal_tests = list(filter(lambda x: not x[2], results))
    
    number_of_tests = len(results) - len(mandatory_tests) 
    number_of_tests_passed = len(list(filter(lambda x: x[0] == x[1], normal_tests))) 
    number_of_positive_tests_passed = len(list(filter(lambda x: x[0] and x[1], normal_tests)))

    failed_mandatory_test = any(filter(lambda x: x[0] != x[1], mandatory_tests))

    if number_of_tests_passed == 0:
        passed = 0.0
    else:
        passed = number_of_tests_passed / float(number_of_tests)


    if failed_mandatory_test or number_of_positive_tests_passed == 0:
        if failed_mandatory_test: 
            print('warning: you have failed a mandatory test')
        if number_of_positive_tests_passed == 0: 
            print('warning: you have not passed at least one positive test')
        
        grade = 5
        color = 91
    elif passed == 1.0:
        grade = 2
        color = 92
    elif passed >= 0.5:
        grade = 3
        color = 93
    elif passed > 0.0:
        grade = 4
        color = 93
    else:
        grade = 5
        color = 91

    print('your grade is: \033[{}m\033[1m'.format(color), end='')
    print_loud('{}'.format(grade), end='')
    print('\033[0m')

    results = [ ]
