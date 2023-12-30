<!--
.. title: PyPy moved to git, github
.. slug: pypy-moved-to-git-github
.. date: 2023-12-29 14:19:55 UTC
.. tags: 
.. category: 
.. link: 
.. description: 
.. type: text
.. author: mattip
-->

PyPy has moved its canonical repo and issue tracker from
<https://foss.heptapod.net/pypy/pypy> to <https://github.com/pypy/pypy>. Obviously,
this means development will now be tracked in git rather than mercurial.

## Motivation

We still feel mercurial is a better version control system. The named branch
model and user interface are superior. But

- foss.heptapod.net is not well tracked in google/bing/duckduckgo
  search, so people find it harder to search for issues in the project

- since heptapod has tightened its spam control, we get reports that
  users create issues only to have them flagged as spam

- open source has become synonymous with github, and we are too small to
  change that

- Much of the current development comes as a reaction to fixing issues.
  Tracking interlocking issues is easier if all the code is on the same
  platform

- The [FAQ](https://doc.pypy.org/en/latest/faq.html#why-doesn-t-pypy-use-git-and-move-to-github)
  presents two arguments against the move. [Github notes](https://git-scm.com/docs/git-notes)
  solves much of point (1): the difficulty of discovering provenance of
  commits, although not entirely. But the main problem is point (2), it turns
  out that __not__ moving to github is an impediment to contribution and issue
  reporting.

- People who wish to continue to use mercurial can use the same method below to
  push to github.

- github is more resource rich than foss.heptapod.net. We could be able to add CI
  jobs to replace some of our aging [buildbot
  infrastructure](https://buildbot.pypy.org).

## Method

The migration required two parts: migrating the code and then migrating the
issues and merge requests.

### Code migration 1: code and notes

I used a [fork of git-remote-hg](https://github.com/mnauw/git-remote-hg) to
create a local git repo with all the changesets. Then I wanted to add a git
note to each commit with the branch it came from. So I prepared a file with two
columns: the git commit hash, and the corresponding branch from mercurial.
Mercurial can describe each commit in two ways: either the commit hash or by a
number index. I used `hg log` to convert an index `i` to the mercurial hash,
and then `git-hg-helper` from `git-remote-hg` to convert the mercurial hash to
a git hash:
```
$(cd pypy-git; git-hg-helper git-rev $(cd ../pypy-hg; hg log -r $i -T"{node}\n"))
```

Then I used `hg log` again to print the mercurial branch for the index `i`:
```
$(cd pypy-hg; hg log -r $i -T'{branch}\n')
```

Putting these two together, I could loop over all the commits by their
numerical index to prepare the file. Then I iterated over each line in the
file, and added the git note. Since the `git note add` command works on the
current HEAD, I needed to checkout each commit in turn and then add the note:
```
git checkout -q <hash> && git notes --ref refs/notes/branch add -m branch:<branch>
```

I could then use `git push --all` to push to github.

### Code migration 2: prepare the branches

PyPy has almost 500 open branches. The code migration created all the branch
HEADs, but `git push --all` did not push them. I needed to check them out and
push each one. So I created a file with all the branch names
```
cd pypy-hg; hg branches | cut -f1 -d" " > branches.txt
```

and then push each one to the github repo

```
while read branch; do git checkout branches/$branch && git push origin branches/$branch; done < branches.txt
```

Note that the branches were named `branches/XXX` by the migration, not `branch/XXX`. This confuses the merge request migration, more about that later.

### Issue and merge request migration

I used the solution from
[node-gitlab-2-github](https://github.com/piceaTech/node-gitlab-2-github) which
worked almost perfectly. It is important to do the conversion on a __private
repo__ otherwise every mention of a sucessfully mapped user name will notify
the user about the transfer. This can be quite annoying for a repo the size of
PyPy with 600 merge requests and over 4000 issues. Issues transfered without a
problem: the script properly retained the issue numbers. However the script
does not convert the mercurial hashes to git hashes, so the bare hashes in
comments show up without a link to the commit. Merge requests are more of a problem:
- the mercurial named branch "disappears" once it is merged, so a merge request
  to a merged branch will not find the target branch name in git. The
  conversion will create an issue instead with the label `gitlab merge request`
- for some reason, the branches created by `git-remote-hg` are called
  `branches/XXX` and not `branch/XXX` as expected by gitlab. This messes up the
  merge request/PR conversion. For some of the branches (open PRs and main
  target branches) I manually created additional branches without the `es`. The
  net result is that open merge requests became open PRs, merged merge requests
  became issues, and closed-not-merged merge requests were not migrated.

### Layered conversions
PyPy already migrated once from bitbucket to heptapod. Many of the issues
reflect the multiple transitions: they have lines like "Created originally on
Bitbucket by XXX" from the first transition, and an additional line "In
Heptapod" from this transition.

## Credits
We would like to express our gratitude to the [Octobus](https://octobus.net/)
team who support heptapod. The transition from bitbucket was quite an effort,
and they have generously hosted our developement since then. We wish them all
the best, and still believe that mercurial should have "won".

## Next steps

While the repo at github is live, there are still a few more things we need to
do:
- Documentation needs an update for the new repo.
- buildbot.pypy.org should also look a the new repo. I hope the code is up to
  the task of interacting with a git repo.
- speed.pypy.org tracks changes, it too needs to reference the new location
- In order to keep tracking branches, we will activate a [github
  action](https://github.com/Julian/named-branch-action) by Julian to add a git
  branch note to each commit.
- Some of the merge requests were not migrated. If someone wants to, they could
  migrate only those once they figure out the branch naming problems.

Additionally, now is the time for all of you to prove the move is worthwhile:
- Star the repo, let others know how to find it
- Help fix some of the open issues or file new ones
- Take advantage of the more familiar workflow to get involved in the project
- Suggest ways to improve the migration: are there things I missed or could
  have done better?

## How will development change?
Heptapod did not allow personal forks, so we were generous with a commit bit to
the main repo. Additionally, we (well, me) have been using a
commit-directly-to-main workflow. We will now be adopting a more structured
workflow. Please fork the repo and submit a pull request for changes. We can now
add some pre-merge CI to check that the PR at least passes the first stage of
translation.

Thanks for helping to make PyPy better.
Matti
