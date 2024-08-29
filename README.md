# pypy.org webpages

This is the source repository for the [pypy.org](https://www.pypy.org) webpages.

You can see the Netlify previews here [![Netlify preview](https://api.netlify.com/api/v1/badges/dcd980ae-706c-4efe-a825-d7f04b054d27/deploy-status)](https://app.netlify.com/sites/keen-mestorf-442210/deploys) 

## Working with the repo to generate new content

The webpages are generated using the static site generator *nikola* (https://getnikola.com/).
To create a new post, first create a virtualenv with `make
venv_nikola/bin/nikola`, then `./venv_nikola/bin/nikola new_post`.

!! The content of `public` (with all helper directories, like js, css, ...) 
   is not written by hand, 
   **please do not modify** - it will be overwritten !!

After you make changes, you can do `make build` to regenerate the pages in
``public/`` for local viewing, but **do not commit these**, they will be
rebuilt and committed via a CI deploy step. You can also do ``make auto`` to
start a server that will serve the pages, and rebuild them when any changes are
made to the sources.

PRs previews will be generated  with Netlify. After pushing a PR, a CI run will
have a "Deploy preview ready!" run, clicking on the "details" link will show the
newly-rendered site preview.


### Comments
Comments to blog posts are generated via the [utterances](https://utteranc.es/)
javascript plugin. The comments appear as issues in the repo.
When viewing the site, a query is made to fetch the comments to the issue with
that name. To comment, users must authorize the utterances app to post on their
behalf using the [GitHub
OAuth](https://developer.github.com/v3/oauth/#web-application-flow) flow.
Alternatively, users can comment on the GitHub issue directly.

[Historic posts](https://morepypy.blogspot.com/) (before the transition to
github in March 2021) were imported with their comments, additional commenting
is disabled.

## Deployment

Any changes to the main branch (including merging PRs) regenerates and pushes
to the gh-pages branch, which is a copy of the `public` directory.

For historical reasons, and in order to allow us to change webpage hosting
easily,  the gh-pages branch is pulled into pypy.org by a cron job on a
psf-hosted instance, see
https://github.com/python/psf-salt/tree/master/salt/pypy-web.

The people with access to the instance are the ones in
https://github.com/python/psf-salt/blob/master/pillar/base/users.sls
with pypy-web access.
