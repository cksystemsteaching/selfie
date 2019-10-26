import os
import sys
import time
import threading

def print_loud(msg, end='\n'):
    quiet_writer = sys.stdout
    sys.stdout = sys.__stdout__

    print(msg, end=end)
    sys.stdout.flush()

    sys.stdout = quiet_writer


def print_usage(options, assignments):
    print('Usage: python3 grader/self.py { option } <test>\n')

    print('Options:')

    width = max(
        map(lambda x: 0 if x[2] is None else len(x[2]), options))

    for option in options:
        print('  {0} {1:{width}}  {2}'.format(
            option[0], option[2] if option[2] is not None else '', option[3], width=width))

    print('')

    def print_assignment_category(category):
        print(category + ' Assignments:')
        
        for assignment in filter(lambda x: x[1] is category, assignments):
            print('  {}'.format(assignment[0]))
        
        print('')

    print_assignment_category('General')
    print_assignment_category('Compiler')
    print_assignment_category('OS')


def print_passed(msg):
    print("\033[92m[PASSED]\033[0m " + msg)


def print_failed(msg, warning, output, command):
    print("\033[91m[FAILED]\033[0m " + msg)
    if command != None:
        print(command)
    if warning != None:
        print("\033[93m > " + warning + " <\033[0m")
    print(' >> ' + output[:-1].replace('\n', '\n >> '))


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
            sys.stdout.write('[  ' + next(self.spinner) + '   ] ' + self.msg)
            sys.stdout.flush()
            time.sleep(0.15)
            sys.stdout.write('\b' * (len(self.msg) + 9))

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

def enter_quiet_mode():
    global quiet_mode
    
    quiet_mode = True
    sys.stdout = open(os.devnull,"w") 


def leave_quiet_mode():
    global quiet_mode 

    if quiet_mode:
        quiet_mode = False
        sys.stdout.flush()
        sys.stdout.close()
        sys.stdout = sys.__stdout__

