import sys
import os

def git_clone(user, repo):
	os.mkdir(user)
	os.chdir(user)
	os.system("git clone git@github.com:" + user + "/" + repo)
	os.chdir(os.path.pardir)

if len(sys.argv) == 3:
	filename = sys.argv[1]

	target = sys.argv[2]
else:
	print "usage: python clone-from-links.py text-file-with-github-links directory-to-clone-repos-into"

	sys.exit(1)

file = open(filename, "r")

os.chdir(target)

for link in file.readlines():
	link = link.replace("\n", "").split("/")
	git_clone(link[3], link[4])

file.close()