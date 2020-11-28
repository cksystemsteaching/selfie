# The Selfie Autograder

[Selfie](http://selfie.cs.uni-salzburg.at) comes with an [autograder](self.py) implemented in Python that features [compiler](../assignments/compiler-assignments.md) and [systems](../assignments/systems-assignments.md) assignments, located in the [assignments](assignments) subdirectory. The autograder is publicly available and meant to be used by students for self-grading before submitting solutions of assignments.

In order to use the autograder [install](../README.md) selfie first.

## Running the Autograder

The autograder reports grades in the range from 2 to 5 where 2 is the best and 4 is the worst passing grade, and 5 is failed. Grade 1 is reserved for submitting solutions that autograde to 2 but also match the code quality and conventions of selfie as detailed below.

The autograder is invoked as follows:

1. Change directory to the root directory of your selfie installation.
2. Invoke the autograder without any command line options: `./grader/self.py`

The autograder responds with its command line options and the list of supported assignments. If it does not respond, your version of Python is probably outdated. Make sure you have at least Python 3.

### For Students

Whenever you changed selfie code you can check if selfie still self-compiles:

1. Change directory to the root directory of your selfie installation.
2. Invoke the autograder with the `self-compile` assignment: `./grader/self.py self-compile`

Selfie still self-compiles if the autograder responds with grade 2. In order to find out about all other assignments supported by the autograder browse the [assignments](assignments).

### For Teachers

The autograder supports bulk grading of an `<assignment>` as follows:

1. Change directory to the root directory of your selfie installation.
2. Create a text file `commit-links.txt` that contains GitHub commit links to which you have read access, one per line and student.
3. Create an empty directory `student-repos`.
4. Invoke the autograder in bulk mode: `./grader/self.py -b commit-links.txt -d student-repos <assignment>`

The autograder clones, for each commit link in `commit-links.txt`, the corresponding repository from GitHub into `student-repos`, grades it for the given `<assignment>`, and reports the grade as well as details on which part of the assignment passes and which does not for each commit link. To suppress the details and just see the grades use `option -q`.

If you subsequently invoke the autograder in bulk mode on `student-repos` again, it only clones repositories for commit links in `commit-links.txt` that are not yet in `student-repos`. Repositories that are already in `student-repos` are just updated from GitHub.

## Submitting Solutions for Grading

Solutions of assignments must be submitted as git commit links to a private clone of the selfie repository hosted on GitHub and exclusively shared with your teacher such as the GitHub user [ckirsch](https://github.com/ckirsch).

### Creating a private clone of selfie

First [install](../README.md) selfie either in the cloud or locally on your machine.

Then, on the web:

1. Create an account on [github.com](https://github.com) unless you already have one.
2. Create a [new](https://github.com/new), empty repository, name it `myselfie`, and set it to private.
3. Invite your teacher, for example, the GitHub user [ckirsch](https://github.com/ckirsch), to the repository as your only collaborator.

And then, in a terminal where your selfie installation is:

1. Change directory to the root directory of your selfie installation (from https://github.com/cksystemsteaching/selfie).
2. Change the `origin` remote name to `upstream`: `git remote rename origin upstream`
3. Add your `myselfie` repository on GitHub as `origin`: `git remote add origin https://github.com/<yourusername>/myselfie.git`
4. Update your installation from `upstream`: `git fetch upstream` (or, initially `git fetch --unshallow upstream` if you are on [repl.it](https://repl.it))
5. Mirror your installation to your `myselfie` repository on GitHub: `git push --mirror origin`
6. Set up the master branch of your installation to push to your `myselfie` repository: `git branch --set-upstream-to=origin/master master`

Your selfie installation as well as your `myselfie` repository on GitHub are successfully set up and ready for submitting solutions of assignments.

### Before working on an assignment

Update your selfie installation to the latest version of the official selfie repository:

1. Change directory to the root directory of your selfie installation.
2. Make sure that the official selfie repository is set as `upstream`: `git remote add upstream https://github.com/cksystemsteaching/selfie.git`
3. Fetch the latest commits from the official selfie repository (`upstream`): `git fetch upstream master`
4. Make sure the master branch of your selfie installation is checked out: `git checkout master`
5. Merge the updated master branch of the official selfie repository into your master: `git merge upstream/master`
6. Depending on how complex the changes made in your selfie installation or the official selfie repository are, you may need to resolve merge conflicts by hand. Please make sure to include both your changes as well as the changes in the official selfie repository.
7. Push your updated master to your `myselfie` repository on GitHub: `git push origin`

You have successfully pulled changes from the official selfie repository into your selfie installation as well as your `myselfie` repository on GitHub.

Note that whenever you need to update your selfie installation but your working tree is not clean according to `git status`, you first need to commit your changes using `git add` and `git commit`. You may also stash your changes using `git stash` and later apply them again using `git stash pop`.

### Working on an assignment

Create a development branch in your selfie installation and work on your solution of an `<assignment>` (regularly committing, pushing, updating, merging):

1. Change directory to the root directory of your selfie installation.
2. Make sure the master branch in your selfie installation is checked out: `git checkout master`
3. Create the development branch off the master branch and check it out: `git checkout -b <developmentbranch>`
4. Work on your solution and use the autograder for feedback. Do not change the autograder in any way! If you discover a bug, please report it to your teacher.
5. Commit your changes regularly using `git add` and `git commit` with the commit messages formatted as `"message [assignment]"` which triggers the autograder on the `<assignment>` as [GitHub Action](https://github.com/cksystemsteaching/selfie/actions) on the next push.
6. Push your changes to your `myselfie` repository on GitHub for backup: `git push -u origin <developmentbranch>`
7. Update your selfie installation to the latest version of the official selfie repository regularly using the above instructions.
8. If you fetched and merged updates go back to the `<developmentbranch>`: `git checkout <developmentbranch>`
9. Merge the updates into your `<developmentbranch>`: `git merge master`

### Submitting your solution

In a terminal where your selfie installation is:

1. Change directory to the root directory of your selfie installation.
2. Make sure the master branch of your selfie installation is checked out: `git checkout master`
3. Merge the `<developmentbranch>` with your solution into the master branch of your selfie installation: `git merge --squash <developmentbranch>`
4. Commit the merged changes: `git commit`
5. Push your updated `master` branch to your `myselfie` repository on GitHub: `git push origin`

Note that the option `--squash` in step 3 is important. It makes sure that all commits on the `<developmentbranch>` are squashed into one commit which improves readability of your solution.

Finally, on the web:

With your solution committed into the master branch of your `myselfie` repository on GibHub in accordance to the above instructions:

1. Go to your `myselfie` repository on GitHub in a browser and click on the `Latest commit` link.
2. Copy the link and make sure that the link is in the form `https://github.com/<yourusername>/myselfie/commit/<commithash>`.
3. Submit the link along with the grade reported by the autograder to your teacher as discussed in class.

If the autograder reports grade 2, you may submit grade 1 provided, in a code review, you are able to demonstrate that your code matches the code quality and conventions of selfie.

Solutions of assignments must be submitted before the deadline stated in class or online. Late submissions will be failed.