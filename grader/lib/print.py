import os
import sys
import time
import threading
from typing import List

from lib.model import Assignment

def println(line='', end='\n', loud=False):
    if loud:
        print_loud(line, end=end)
    else:
        print(line, end=end)


def print_loud(msg, end='\n'):
    quiet_writer = sys.stdout
    sys.stdout = sys.__stdout__

    println(msg, end=end)
    sys.stdout.flush()

    sys.stdout = quiet_writer


def print_usage(options, assignments: List[Assignment]):
    println('Usage: python3 grader/self.py { option } <test>\n')

    println('Options:')

    width = max(
        map(lambda x: 0 if x[2] is None else len(x[2]), options))

    for option in options:
        println('  {0} {1:{width}}  {2}'.format(
            option[0], option[2] if option[2] is not None else '', option[3], width=width))

    println()

    def print_assignment_of_lecture(lecture):
        println(lecture + ' Assignments:')

        for assignment in filter(lambda x: x.lecture is lecture, assignments):
            println('  {}'.format(assignment.name))

        println()

    print_assignment_of_lecture('General')
    print_assignment_of_lecture('Compiler')
    print_assignment_of_lecture('OS')


def print_grade(grade):
    colors = {'2': 92, '3': 93, '4': 93, '5': 91}

    println('your grade is: \033[{}m\033[1m'.format(
        colors[str(grade)]), end='')
    println('{}'.format(grade), end='', loud=True)
    println('\033[0m')


def print_passed(msg):
    println("\033[92m[PASSED]\033[0m " + msg)


def print_failed(msg, warning, output, command):
    println("\033[91m[FAILED]\033[0m " + msg)
    if command != None:
        println(command)
    if warning != None:
        println("\033[93m > " + warning + " <\033[0m")
    println(' >> ' + output[:-1].replace('\n', '\n >> '))


def print_message(message, end='\n', loud=False):
    println(message, end=end, loud=loud)


def print_warning(warning):
    println('warning: ' + warning)


def print_error(error):
    println(error)


class SpinnerThread(threading.Thread):
    def __init__(self, msg):
        def spinning_cursor():
            while True:
                for cursor in '|/-\\':
                    yield cursor

        threading.Thread.__init__(self)
        self.msg = msg
        self.should_stop = False
        self.spinner = spinning_cursor()

    def stop(self):
        self.should_stop = True

    def run(self):
        while not self.should_stop:
            println('[  ' + next(self.spinner) + '   ] ' + self.msg, end='')
            sys.stdout.flush()
            time.sleep(0.15)
            println('\b' * (len(self.msg) + 9), end='')

        sys.stdout.flush()


spinner_thread = None


def print_processing(msg):
    global spinner_thread

    spinner_thread = SpinnerThread(msg)
    spinner_thread.daemon = True  # die when parent dies
    spinner_thread.start()


def stop_processing_spinner():
    global spinner_thread

    if spinner_thread != None:
        spinner_thread.stop()
        spinner_thread.join()
        spinner_thread = None


quiet_mode = False

def is_in_quiet_mode():
    return quiet_mode

def enter_quiet_mode():
    global quiet_mode

    quiet_mode = True
    sys.stdout = open(os.devnull, "w")


def leave_quiet_mode():
    global quiet_mode

    if quiet_mode:
        quiet_mode = False
        sys.stdout.flush()
        sys.stdout.close()

    sys.stdout = sys.__stdout__
