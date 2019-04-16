#!/usr/bin/env python3

import sys
import os

if len(sys.argv) > 2:
  target = sys.argv[1]

  command = ' '.join(sys.argv[2:])
else:
  print('usage: python3 run-in-user-repos.py parent-directory command-with-any-number-of-options')

  sys.exit(1)

os.chdir(target)

for user in next(os.walk(os.path.curdir))[1]:
  os.chdir(user)

  for repo in next(os.walk(os.path.curdir))[1]:
    print('\n\n' + user + '/' + repo + ':')

    os.chdir(repo)

    os.system(command)

    os.chdir(os.path.pardir)

  os.chdir(os.path.pardir)