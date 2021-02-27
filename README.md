# pypy.org webpages

This is the source repository for the pypy.org webpages.

The webpages are generated using the static site generator *nikola* (https://getnikola.com/).

To change content of the pages, please change the 
files in the `posts`, `files` and `pages` directories only. 

!! The content of `public` (with all helper directories, like js, css, ...) 
   is not written by hand, 
   **please do not modify** - it will be overwritten !!

After you make changes, you can do `make build` to regenerate the pages in
``public/`` for local viewing, but **do not commit these**, they will be
rebuilt and commited via a CI deploy step. You can also do ``make auto`` to
start a server that will serve the pages, and rebuild them when any changes are
mede ot the sources.

PRs can be previewed with Netlify. Any changes to the master branch (including
merging PRs) regenerates the gh-pages branch, which is a copy of the `public`
directory.

For historical reasons, and in order to allow us to change webpage hosting
easily,  the gh-pages branch is pulled into pypy.org by a cron job on a
psf-hosted instance, see
https://github.com/python/psf-salt/tree/master/salt/pypy-web.

The people with access to the instance are the ones in
https://github.com/python/psf-salt/blob/master/pillar/base/users.sls
with pypy-web access.
