import sys
import os

def run_in(directory):
	os.chdir(directory)
	os.system(command)
	os.chdir(os.path.pardir)

if len(sys.argv) > 1:
	command = ' '.join(sys.argv[1:])
else:
	command = 'ls'

for directory in next(os.walk(os.path.curdir))[1]:
	run_in(directory)