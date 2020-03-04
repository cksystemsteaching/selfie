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

### Creating a Private Clone of Selfie

First [install](../README.md) selfie either in the cloud or locally on your machine unless you have already done that.

Then, on the web:

0. Create an account on [github.com]() unless you already have one.
1. Create a [new](https://github.com/new), empty repository, name it `myselfie`, and set it to private.
2. Invite your teacher, for example, the GitHub user [ckirsch](https://github.com/ckirsch), to the repository as your only collaborator.

And then, in a terminal where your selfie installation is:

0. Change directory to the root directory of your selfie installation.
1. Change the `origin` remote name to `upstream`: `git remote rename origin upstream`
2. Add your `myselfie` repository on GitHub as `origin`: `git remote add origin https://github.com/<yourusername>/myselfie.git`
3. Update your installation from `upstream`: `git fetch --unshallow upstream`
4. Mirror your installation to your `myselfie` repository on GitHub: `git push --mirror origin`
5. Setup the master branch of your installation to push to your `myselfie` repository: `git branch --set-upstream-to=origin/master master`

Your selfie installation as well as your `myselfie` repository on GitHub are successfully set up and ready for submitting solutions of assignments.

### Working on Assignments

#### Keeping your selfie installation up-to-date with the official selfie repository

0. Change directory to the root directory of your selfie installation.
1. Make sure that the official selfie repository is set as `upstream`: `git remote add upstream https://github.com/cksystemsteaching/selfie.git`
2. If your working tree is not clean according to `git status`, commit your changes using `git commit` or save them for later using `git stash`.
3. Fetch the latest commits from the official selfie repository (`upstream`): `git fetch upstream master`
4. Merge selfie's updated master branch into your master: `git merge upstream/master`
5. Depending on how complex the changes made in your selfie installation or the official selfie repository are, you may need to resolve merge conflicts by hand. Please make sure to include both your changes as well as the changes in the official selfie repository.
6. Push your updated master to your `myselfie` repository on GitHub: `git push origin`
7. If you have stashed your changes for later in Step 2, apply them again using `git stash pop`.

You have successfully pulled changes from the official selfie repository into your selfie installation as well as your `myselfie` repository on GitHub.