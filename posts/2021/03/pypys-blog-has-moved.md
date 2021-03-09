<!--
.. title: PyPy's blog has moved
.. slug: pypys-blog-has-moved
.. date: 2021-03-09 11:03:09 UTC
.. tags: 
.. category: 
.. link: 
.. description: 
.. type: text
.. author: mattip
-->

For many years, PyPy has been publishing blog posts at
https://morepypy.blogspot.com. From now on, the posts will be here, at
https://pypy.org/blog. The RSS feed is https://pypy.org/rss.xml. The original
content has been migrated to the newer site, including comments.

<!-- TEASER_END -->

Among the motivations for the move were:

### One site to rule them all
Adding the blog posts here seems like a natural extension of the web site
rather than outsourcing it to a third-party. Since the site is generated using
the static site generator [nikola](https://getnikola.com/) from the github repo
https://github.com/pypy/pypy.org, we also have good source control for the
content.

### CI previews, and github

Those of you who follow PyPy may note something new in the URL for the repo:
until now PyPy has been using [mercurial](https://mercurial-scm.org) as hosted
on https://foss.heptapod.net.  While [heptapod](https://heptapod.net/) (a
community driven effort to bring mercurial support to GitLab™) does provide a
GitLab CI runner for the open source offering, on github we can use netlify for
previews. Hopefully the move to the more popular github platform will encourage
new contributors to publish their success stories around using PyPy and
the RPython toolchain.

### Comments

Comments to blog posts are generated via the [utterances](https://utteranc.es/)
javascript plugin. The comments appear as issues in the repo.
When viewing the site, a query is made to fetch the comments to the issue with
that name. To comment, users must authorize the utterances app to post on their
behalf using the [GitHub
OAuth](https://developer.github.com/v3/oauth/#web-application-flow) flow.
Alternatively, users can comment on the GitHub issue directly. The interaction
with github for authentication and moderation seems more natural than the
manual moderation required on blogspot.

### Please prove to us that the move is worth it

Help us with guest blog posts, and PRs to improve the styling of the site. One
already [open issue](https://github.com/pypy/pypy.org/issues/5) is that the
navbar needlessly uses javascript, help to keep the responsive style in pure
CSS is welcome. The theme could also use tweaking.

But more importantly, we want to hear from you.  Guest blog posts about
PyPy are welcome. Just follow the directions in the repo's README to create a
PR with your favorite PyPy story.

The PyPy Team
