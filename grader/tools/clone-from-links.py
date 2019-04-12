#!/usr/bin/env python3

import sys
import os

if len(sys.argv) == 3:
  filename = sys.argv[1]

  target = sys.argv[2]
else:
  print('usage: python3 clone-from-links.py text-file-with-github-links directory-to-clone-repos-into')

  sys.exit(1)

file = open(filename, 'r')

os.chdir(target)

for link in file.readlines():
  splitted_link = link.replace('\n', '').split('/')

  user = splitted_link[3]
  repo = splitted_link[4]

  os.mkdir(user)

  os.chdir(user)

  os.system('git clone https://github.com/' + user + '/' + repo)

  os.chdir(os.path.pardir)

file.close()