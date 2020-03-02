# Instructions for students

## Setting up your environment

In order to implement and hand in assignments, each student needs to create a private fork of selfie and enroll into the course on repl.it

> :warning: **Warning:**
>
> Ensure that both the repl.it project as well as your GitHub repository are set to private. Failing to do so results in your code being publicly accessible and thus prone for being copy-pasted.

0. Set up a private GitHub repository:
   1. Create a new repository on GitHub by clicking onto the plus icon in the title bar and selecting `New repository`. Enter a name and make sure to select `Private`.
   2. Go to Settings -> Collaborators and add `ckirsch` as a collaborator
1. Enroll into the repl.it class using the following link: https://repl.it/classroom/invite/mW8BOP4
2. In the classroom dashboard, select Projects -> Selfie. This is a public copy (for now) on your account.
3. In the console on the right side, set up your private git repo as `origin`:
   1. Change selfie's remote name to `upstream`: `git remote rename origin upstream`
   2. Add your own repository as `origin`: `git remote add origin https://github.com/<your_username>/<your_repo>.git`
   3. Update your repository from `upstream`: `git fetch --unshallow upstream`
   4. Mirror the repository to your private repository: `git push --mirror origin`
   5. Setup the master branch to push to your repository: `git branch --set-upstream-to=origin/master master`
4. Set your repl.it project to private:
   1. In the top-left corner: Go to Menu -> My Repls
   2. Click onto the three-dot menu of your Selfie repl and click onto the `public` toggle to set your to private
   3. Make sure that there is a lock icon after the repl's name to ensure it is set to private.
5. Your repl.it copy as well as your GitHub repository were successfully set up and you are ready to start your assignment



## Keeping your repository up-to-date with selfie's master

By adding selfie as upstream it is possible to merge and add changes made to the original selfie's repository into your copy:

0. Make sure you've committed all changes by using `git status`. If your work tree is not clean, commit your changes using `git commit` or save them for later using `git stash`
1. Fetch the latest commits from the original selfie repository (upstream): `git fetch upstream master`
2. Merge selfie's updated master branch into your master: `git merge upstream/master`
3. Depending on how complex the changes made in your repository or selfie's repository are, you may need to resolve merge conflicts by hand. Please make sure to include both your changes as well as original selfie's changes.
4. Push your updated master to your private repository: `git push origin`
5. If you have stashed your changes for later in step 0, apply them again using `git stash pop`.
6. You have successfully pulled changes from the original selfie repository into your local copy as well as your GitHub repository.
