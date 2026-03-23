<!--
.. title: Using Claude to fix PyPy3.11 test failures securely
.. slug: using-claude-to-fix-pypy311-test-failures-securely
.. date: 2026-03-23 10:27:55 UTC
.. tags: AI
.. category:
.. link:
.. description:
.. type: rst
.. author: mattip
-->

I got access to Claude Max for 6 months, as a promotional move Anthropic made
to Open Source Software contributors. My main OSS impact is as a maintainer for
NumPy, but I decided to see what claude-code could to for PyPy's failing 3.11
tests. Most of these failures are edge cases: error messages that differ from
CPython, or debugging tools that fail in certain cases. I was worried about
letting an AI agent loose on my development machine. I noticed `a post`_ by
Patrick McCanna (thanks Patrick!) that pointed to using bubblewrap to
sandbox the agent. So I set it all up and (hopefully securely) pointed
claude-code at some tests.

.. _`a post`: https://patrickmccanna.net/a-better-way-to-limit-claude-code-and-other-coding-agents-access-to-secrets/

.. TEASER_END: Read more to find out how it went


Setting up
----------

There were a few steps to make sure I didn't open myself up to obvious gotchas.
There are stories about agents wiping out data bases, or deleting mail boxes.

Bubblewrap
==========

First I needed to see what bubblewrap does. I followed the instructions in the
blog post to set things up with some minor variations:

.. code:: bash

  sudo apt install bubblewrap


I couldn't run ``bwrap``. After digging around a bit, I found I needed to add
an exception for appamor on Ubuntu 24.04:

.. code:: bash

    sudo bash -c 'cat > /etc/apparmor.d/bwrap << EOF
    abi <abi/4.0>,
    include <tunables/global>

    profile bwrap /usr/bin/bwrap flags=(unconfined) {
      userns,
    }
    EOF'
    sudo apparmor_parser -r /etc/apparmor.d/bwrap

Then ``bwrap`` would run. It is all locked down by default, so I opened up some
exceptions. The arguments are pretty self-explanatory. Ubuntu spreads the
executables around the operating system, so I needed access to various
directories. I wanted a ``/tmp`` for running pytest. I also wanted the prompt
to reflect the use of bubblewrap, so changed the ``hostname``:

.. code:: bash

  cat << 'EOL' >> ./run_bwrap.sh
    function call_bwrap() {
      bwrap \
        --ro-bind /usr /usr \
        --ro-bind /etc /etc \
        --ro-bind /run /run \
        --symlink usr/lib /lib \
        --symlink usr/lib64 /lib64 \
        --symlink usr/bin /bin \
        --proc /proc \
        --dev /dev \
        --bind $(pwd) $(pwd) \
        --chdir $(pwd) \
        --unshare-user --unshare-pid --unshare-ipc --unshare-uts --unshare-cgroup \
        --die-with-parent \
        --hostname bwrap \
        --tmpfs /tmp \
        /bin/bash "$@"
    }
  EOL

  source ./run_bwrap.sh
  call_bwrap
  # now I am in a sandboxed bash shell
  # play around, try seeing other directories, getting sudo, or writing outside
  # the sandbox
  exit

I did not do ``--unshare-network`` since, after all, I want to use claude and
that needs network access. I did add rw access to ``$(pwd)`` since I want it to
edit code in the current directory, that is the whole point.

Basic claude
============

After trying out bubblewrap and convincing myself it does actually work, I
installed claude code

.. code:: bash

    curl -fsSL https://claude.ai/install.sh | bash

Really Anthropic, this is the best way to install claude? No dpkg?

I ran claude once (unsafely) to get logged in. It opened a webpage, and saved
the login to the ``oathAccount`` field in ``~/.claude.json``. Now I changed my
bash script to this to get claude to run inside the bubblewrap sandbox:

.. code:: bash

  cat << 'EOL' >> ./run_claude.sh
    claude-safe() {
      bwrap \
        --ro-bind /usr /usr \
        --ro-bind /etc /etc \
        --ro-bind /run /run \
        --ro-bind "$HOME/.local/share/claude" "$HOME/.local/share/claude" \
        --symlink usr/lib /lib \
        --symlink usr/lib64 /lib64 \
        --symlink usr/bin /bin \
        --symlink "$HOME/.local/share/claude/versions/2.1.81" "$HOME/.local/bin/claude" \
        --proc /proc \
        --dev /dev \
        --bind $(pwd) $(pwd) \
        --bind "$HOME/.claude" "$HOME/.claude" \
        --bind "$HOME/.claude.json" "$HOME/.claude.json" \
        --chdir $(pwd) \
        --unshare-user --unshare-pid --unshare-ipc --unshare-uts --unshare-cgroup \
        --die-with-parent \
        --hostname bwrap \
        --tmpfs /tmp \
        --setenv PATH "$HOME/.local/bin:$PATH" \
        claude "$@"
    }
  EOL

  source ./run_claude.sh
  claude-safe

Now I can use claude. Note it needs some more directories in order to run. This
script hard-codes the version, in the future YMMV. I want it to be able to look
at github, and also my local checkout of cpython so it can examine differences.
I created a read-only token by clicking on my avatar in the upper right corner
of a github we page, then going to Settings → Developer settings → Personal
access tokens → Fine-grained tokens → Generate new token. Since pypy is in the
pypy org, I used "Repository owner: pypy", "Repository access: pypy (only)" and
"Permissions: Contents". Then I made doubly sure the token permissions were
read-only. And checked again. Then I copied the token to the bash script. I
also added a ``ro-bind`` to the cpython checkout, so I could tell claude code
where to look for CPython implementations of missing PyPy functionality.

.. code:: bash

        --ro-bind "$HOME/oss/cpython" "$HOME/oss/cpython" \
        --setenv GH_TOKEN "hah, sharing my token would not have been smart" \

Claude /sandbox
===============

Claude comes with its own sandbox, configured by using the ``/sandbox`` command.
I chose the defaults, which prevents malicious code in the repo from accessing
the file system and the network. I was missing some packages to get this to
work. Claude would hang until I installed them, and I needed to kill it with
``kill``.

.. code:: bash

    sudo apt install socat
    sudo npm install -g @anthropic-ai/sandbox-runtime

Final touches
=============

One last thing that I discovered later: I needed to give claude access to some
grepping and git tools. While git should be locked down externally so it
cannot push to the repo, I do want claude to look at other issues and pull
requests in read-only mode. So I added a local ``.claude/settings.json`` file
inside the repo (see below for which directory to do this):

.. code:: json

    {
      "permissions": {
        "allow": [
          "Bash(sed*)",
          "Bash(grep*)",
          "Bash(cat*)",
          "Bash(find*)",
          "Bash(rg*)",
          "Bash(python*)",
          "Bash(pytest*)"
        ]
      }
    }

Then I made git ignore it, even when doing a ``git clean``, in a local (not part
of the repo) configuration

.. code:: bash

  echo -n .claude >> ~/.config/git/ignore

What about ``git push``?
========================

I don't want claude messing around with the upstream repo, only read access. But
I did not actively prevent ``git push``. So instead of using my actual pypy
repo, I cloned it to a separate directory and did not add a remote pointing to
github.com.


Fixing tests - easy
-------------------

Now that everything is set up (I hope I remembered everything), I could start
asking questions. The technique I chose was to feed claude the whole test
failure from the buildbot. So starting from the `buildbot py3.11 summary`_,
click on one of the ``F`` links and copy-paste all that into the claude prompt.
It didn't take long for claude to come up with solutions for the long-standing
`ctype error missing exception`_ which turned out to be due to an missing error
trap when already handling an error.

Also a `CTYPES_MAX_ARGCOUNT check`_ was
missing. At first, claude wanted to change the ctypes code from CPython's stdlib,
and so I had to make it clear that claude was not to touch the files in
``lib-python``. They are copied verbatim from CPython and should not be
modified without really good reasons.

The `fix to raise`_ ``TypeError`` rather
than ``Attribute Error`` for deleting ctype object's ``value`` was maybe a little
trickier: claude needed to create its own ``property`` class and use it in
assignments.

The `fix for a failing test`_ for a correct ``repr`` of a ctypes array was a
little more involved.  Claude needed to figure out that ``newmemoryview`` was
raising an exception, dive into the RPython implementation and fix the problem,
and then also fix a pure-python ``__buffer__`` shape edge case error.

There were more, but you get the idea. With a little bit of coaching, and by showing
claude where the CPython implementation was, more tests are now passing.

Fixing tests - harder
---------------------

PyPy has a HPy backend. There were some test failures that were
easy to fix (a handle not being closed, an annotation warning). But the big one
was a problem with the context tracking before and after ffi function calls. In
debug mode there is a check that the ffi call is done using the correct HPy
context. It turns out to be tricky to hang on to a reference to a context in
RPython since the context RPython object is pre-built. The solution, which took
quite a few tokens and translation cycles to work out, was to assign the
context on the C level, and have a getter to fish it out in RPython.

Conclusion
==========

I started this journey not more than 24 hours ago, after some successful
sessions using claude to refactor some web sites off hosting platforms and make
them static pages. I was impressed enough to try coding with it from the
terminal. It helps that I was given a generous budget to use Anthropic's tool.

Claude seems capable of understanding the layers of PyPy: from the pure python
stdlib to RPython and into the small amount of C code. I even asked it to
examine a segfault_ in the recently released PyPy7.3.21, and it seems to have
found the general area where there was a latent bug in the JIT.

Like any tool, agentic programming must be used carefully to make sure it
cannot do damage. I hope I closed the most obvious foot-guns, if you have other
ideas of things I should do to protect myself while using an agent like this, I
would love to hear about them.


.. _`buildbot py3.11 summary`: https://buildbot.pypy.org/summary?branch=py3.11
.. _`ctype error missing exception`: https://github.com/pypy/pypy/commit/9e8e121b545dbea3f26ca436ae8a797617904306#diff-ab042b3dd16bf22b7e3d8595f182ad39d3823d76b414da7debe96081a884d16bR64-R330
.. _`CTYPES_MAX_ARGCOUNT check`: https://github.com/pypy/pypy/commit/9e8e121b545dbea3f26ca436ae8a797617904306#diff-ab042b3dd16bf22b7e3d8595f182ad39d3823d76b414da7debe96081a884d16bR64-R53
.. _`fix to raise`: https://github.com/pypy/pypy/commit/39ca7a1def272742e8aafd2a649ed4f8fed7038d
.. _`fix for a failing test`: https://github.com/pypy/pypy/commit/e0e401699c20a92d8db657879183c68ea44246b4
.. _segfault: https://github.com/pypy/pypy/issues/5398
