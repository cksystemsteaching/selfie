import sys
import os

if len(sys.argv) == 5:
	links      = sys.argv[1]
	selfiedir  = sys.argv[2]
	reposdir   = sys.argv[3]
	assignment = sys.argv[4]
else:
	print "usage: python grade-from-links.py text-file-with-github-links selfie-directory repos-directory assignment"

	sys.exit(1)

file = open(links, "r")

os.chdir(reposdir)

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
	os.system("python3 " + selfiedir + "/grader/self.py " + assignment)

	os.chdir(os.path.pardir)
	os.chdir(os.path.pardir)

file.close()