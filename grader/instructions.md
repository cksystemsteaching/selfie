# The Selfie Autograder How-to

[Selfie](http://selfie.cs.uni-salzburg.at) comes with an [autograder](self.py) implemented in Python that features compiler and operating systems [assignments](). The autograder is publicly available and meant to be used by students for self-grading before submitting solutions of assignments.

In order to use the autograder [install](../README.md) selfie first.

## Running the Autograder

The autograder reports grades in the range from 2 to 5 where 2 is the best and 4 is the worst passing grade, and 5 is failed. Grade 1 is reserved for submitting solutions that autograde to 2 but also match the code quality and conventions of selfie as detailed below.

TODO: instructions on how to use the autograder

### For Students

### For Teachers

## Submitting Solutions for Grading

Solutions of assignments must be submitted as git commit links to a private clone of the selfie repository hosted on GitHub and exclusively shared with your teacher such as the GitHub user [ckirsch](https://github.com/ckirsch).

### Creating a private clone of selfie

First [install](../README.md) selfie either in the cloud or locally on your machine unless you have already done that.

Then, on the web:

1. Create an account on [github.com]() unless you already have one.
2. Create a [new](https://github.com/new), empty repository, name it `myselfie`, and set it to private.
3. Invite your teacher, for example, the GitHub user [ckirsch](https://github.com/ckirsch), to the repository as your only collaborator.

And then, in a terminal where your selfie installation is:

1. Change directory to the root directory of your selfie installation.
2. Change the `origin` remote name to `upstream`: `git remote rename origin upstream`
3. Add your `myselfie` repository on GitHub as `origin`: `git remote add origin https://github.com/<yourusername>/myselfie.git`
4. Update your installation from `upstream`: `git fetch --unshallow upstream`
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

Create a development branch in your selfie installation and work on your solution of an assignment (regularly committing, pushing, updating, merging):

1. Make sure the master branch in your selfie installation is checked out: `git checkout master`
2. Create the development branch off the master branch and check it out: `git checkout -b <developmentbranch>`
3. Work on your solution and use the autograder for feedback. Do not change the autograder in any way! If you discover a bug, please report it to your teacher.
4. Commit your changes regularly using `git add` and `git commit`.
5. Push your changes to your `myselfie` repository on GitHub for backup: `git push -u origin`
6. Update your selfie installation to the latest version of the official selfie repository regularly using the above instructions.
7. If you fetched and merged updates go back to the `<developmentbranch>`: `git checkout <developmentbranch>`
8. Merge the updates into your `<developmentbranch>`: `git merge master`

### Submitting your solution

In a terminal where your selfie installation is:

1. Make sure the master branch of your selfie installation is checked out: `git checkout master`
2. Merge the `<developmentbranch>` with your solution into the master branch of your selfie installation: `git merge --squash <developmentbranch>`

Note that the option `--squash` is important. It makes sure that all commits on the `<developmentbranch>` are squashed into one commit which improves readability of your solution.

Finally, on the web:

With your solution committed into the master branch of your `myselfie` repository on GibHub in accordance to the above instructions:

1. Go to your `myselfie` repository on GitHub in a browser and click on the `Latest commit` link.
2. Copy the link and make sure that the link is in the form `https://github.com/<yourusername>/myselfie/commit/<commithash>`.
3. Submit the link along with your self-grade to your teacher as discussed in class.

Solutions of assignments must be submitted before the deadline stated in class or online. Late submissions will be failed.