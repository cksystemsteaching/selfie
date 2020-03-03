# Setting up a private repository

In order to implement and hand in assignments, each student needs to create and fork a recent version of Selfie into a private GitHub repository. GitHub does not support creating a private fork of public repositories, thus requiring some manual set-up.

> :warning: **Warning:**
>
> Ensure that both the repl.it project as well as your GitHub repository are set to private. Failing to do so results in your code being publicly accessible and thus prone for being copy-pasted.

## Forking the repository and initial setup

To follow these steps, you are expected to have cloned Selfie to your working space. In repl.it, Selfie is automatically cloned. Locally, you need to `git clone` the Selfie repository.

0. Open a terminal and change directory to the cloned Selfie directory
1. Set up your private git repo as `origin`:
   1. Change selfie's remote name to `upstream`: `git remote rename origin upstream`
   2. Add your own repository as `origin`: `git remote add origin https://github.com/<your_username>/<your_repo>.git`
   3. Update your repository from `upstream`: `git fetch --unshallow upstream`
   4. Mirror the repository to your private repository: `git push --mirror origin`
   5. Setup the master branch to push to your repository: `git branch --set-upstream-to=origin/master master`
3. Your GitHub repository was successfully set up and you are ready to start your assignment

## Checking out your repository (with Selfie as upstream)

If you obtain a fresh clone of your private repository, you need to add Selfie's repository as upstream to be able to update your repository.

0. Open a terminal and change directory to the directory where you cloned your repository to.
1. Add selfie's repository as `upstream`: `git remote add upstream https://github.com/cksystemsteaching/selfie.git`
2. You are now able to update your private repository

## Keeping your repository up-to-date with selfie's master

By adding selfie as upstream it is possible to merge and add changes made to the original selfie's repository into your copy:

0. Make sure you've committed all changes by using `git status`. If your work tree is not clean, commit your changes using `git commit` or save them for later using `git stash`
1. Fetch the latest commits from the original selfie repository (upstream): `git fetch upstream master`
2. Merge selfie's updated master branch into your master: `git merge upstream/master`
3. Depending on how complex the changes made in your repository or selfie's repository are, you may need to resolve merge conflicts by hand. Please make sure to include both your changes as well as original selfie's changes.
4. Push your updated master to your private repository: `git push origin`
5. If you have stashed your changes for later in step 0, apply them again using `git stash pop`.
6. You have successfully pulled changes from the original selfie repository into your local copy as well as your GitHub repository.
