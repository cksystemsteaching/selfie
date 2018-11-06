import sys
import os

if len(sys.argv) == 4:
	filename   = sys.argv[1]
	target     = sys.argv[2]
	assignment = sys.argv[3]
else:
	print "usage: python grade-from-links.py text-file-with-github-links directory-where-repos-are assignment"

	sys.exit(1)

file = open(filename, "r")

os.chdir(target)

for link in file.readlines():
	link = link.replace("\n", "").split("/")

	user   = link[3]
	repo   = link[4]
	commit = link[6]

	print "\n\n" + user + "/" + repo + ":"

	os.chdir(user)
	os.chdir(repo)

	os.system("git fetch")
	os.system("git checkout " + commit)
	os.system("make")
	os.system("python3 grader/self.py " + assignment)

	os.chdir(os.path.pardir)
	os.chdir(os.path.pardir)

file.close()