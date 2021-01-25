import os
import sys
import time
import threading
from typing import List, Tuple

from lib.model import Assignment
from lib.string import nfind, nrfind

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


def print_grade(grade):
    colors = {'2': 92, '3': 93, '4': 93, '5': 91}

    println('your grade is: \033[{}m\033[1m'.format(
        colors[str(grade)]), end='')
    println('{}'.format(grade), end='', loud=True)
    println('\033[0m')


def print_passed(msg):
    println("\033[92m[PASSED]\033[0m " + msg)


def print_failed(msg, warning, output: str, command):
    println("\033[91m[FAILED]\033[0m " + msg)
    if command != None:
        println(command)
    if warning != None:
        println("\033[93m > " + warning + " <\033[0m")

    # The output has to be truncated if neither head nor tail are unlimited
    if get_truncate_head() != -1 and get_truncate_tail() != -1:
        # and the amount of lines in the output exceeds the bounds
        totalMaxLines = get_truncate_head() + get_truncate_tail()
        outputLines = output.count('\n')
        if outputLines > totalMaxLines:
            omittedLines = outputLines - totalMaxLines
            head = nfind(output, '\n', get_truncate_head())
            tail = nrfind(output, '\n', get_truncate_tail() + 1) # +1 due to empty last line


            output = output[:head+1] + \
                '----------8<---------- [{:3} lines truncated] ---------->8----------\n'.format(omittedLines) + \
                output[tail+1:]


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


truncate_lines: Tuple[int, int] = (-1, -1)

def get_truncate_head() -> int:
    global truncate_lines
    return truncate_lines[0]

def get_truncate_tail() -> int:
    global truncate_lines
    return truncate_lines[1]

def set_truncate_head(head: int):
    global truncate_lines
    truncate_lines[0] = head

def set_truncate_tail(tail: int):
    global truncate_lines
    truncate_lines[1] = tail

def set_truncate(head: int, tail: int):
    global truncate_lines
    truncate_lines = (head, tail)

def reset_truncate():
    global truncate_lines
    truncate_lines = (-1, -1)
