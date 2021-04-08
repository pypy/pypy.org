.. title: PyPy - Features
.. slug: features
.. date: 2019-12-28 16:14:02 UTC
.. tags: 
.. category: 
.. link: 
.. author: The PyPy Team
.. description: What is PyPy and what are its features

**PyPy** is a replacement for CPython.  It is built using the RPython
language that was co-developed with it.  The main reason to use it
instead of CPython is speed: it runs generally faster (see next section).

**PyPy** implements **Python 2.7.18, and 3.7.10**.
It supports all of the core language, passing the Python 2.7 test suite
and almost all of the 3.7 test suite (with minor modifications) It supports most of
the commonly used Python standard library modules. For known differences with
CPython, see our `compatibility`_ page.

The following CPU architectures are supported and maintained:

* `x86 (IA-32)`_ and `x86_64`_ 
* `ARM`_ platforms (ARMv6 or ARMv7, with VFPv3)
* `AArch64`_
* `PowerPC`_ 64bit both little and big endian
* `System Z (s390x)`_

PyPy's x86 version runs on several operating systems, such as Linux
(32/64 bits), Mac OS X (64 bits), Windows (32 bits), OpenBSD, FreeBSD.
All non-x86 versions are only supported on Linux.

If you are interested in helping, see our `howtohelp`_ page.

.. _`compatibility`: compat.html
.. _`x86 (IA-32)`: http://en.wikipedia.org/wiki/IA-32
.. _`x86_64`: http://en.wikipedia.org/wiki/X86_64
.. _`ARM`: http://en.wikipedia.org/wiki/ARM
.. _`AArch64`: http://en.wikipedia.org/wiki/AArch64
.. _`PowerPC`: https://de.wikipedia.org/wiki/PowerPC
.. _`System Z (s390x)`: https://de.wikipedia.org/wiki/System/390
.. _`howtohelp`: howtohelp.html

.. |---| unicode:: U+2014  .. em dash, trimming surrounding whitespace
   :trim:

The main features of PyPy:
--------------------------

Speed
=====

Our `main executable`_ comes with a Just-in-Time compiler.  It is
`really fast`_ in running most benchmarks |---| including very large and
complicated Python applications, not just 10-liners.

There are two cases that you should be aware where PyPy will *not* be
able to speed up your code:

* Short-running processes: if it doesn't run for at least a few seconds,
  then the JIT compiler won't have enough time to warm up.

* If all the time is spent in run-time libraries (i.e. in C functions),
  and not actually running Python code, the JIT compiler will not help.

So the case where PyPy works best is when executing long-running
programs where a significant fraction of the time is spent executing
Python code.  This is the case covered by the majority of `our
benchmarks`_, but not all of them --- the goal of PyPy is to get speed
but still support (ideally) any Python program.

.. _`main executable`: download.html#with-a-jit-compiler
.. _`really fast`: http://speed.pypy.org/
.. _`our benchmarks`: http://speed.pypy.org/


Memory usage
============

Memory-hungry Python programs (several hundreds of MBs or more) might
end up taking less space than they do in CPython.  It is not always
the case, though, as it depends on a lot of details.  Also note that
the baseline is higher than CPython's.


Stackless
=========

Support for Stackless_ and greenlets are now integrated in the normal
PyPy.  More detailed information is available here__.

.. _Stackless: http://www.stackless.com/
.. __: http://doc.pypy.org/en/latest/stackless.html


Other features
==============

PyPy has many secondary features and semi-independent
projects.  We will mention here:

* **Other languages:**  we also implemented other languages that makes
  use of our RPython toolchain: Prolog_ (almost complete), as
  well as Smalltalk_, JavaScript_, Io_, Scheme_ and Gameboy_.

  There is also a Ruby implementation called Topaz_ and a PHP implementation
  called HippyVM_.


Sandboxing
==========

PyPy's *sandboxing* is a working prototype for the idea of running untrusted
user programs. Unlike other sandboxing approaches for Python, PyPy's does not
try to limit language features considered "unsafe". Instead we replace all
calls to external libraries (C or platform) with a stub that communicates
with an external process handling the policy.

.. note::

    **Please be aware that it is a prototype only.**  It needs work to become  
    more complete, and you are welcome to help.  In particular, almost none     
    of the extension modules work (not even ``time`` ), and ``pypy_interact``
    is merely a demo.  Also, a more complete system would include a way        
    to do the same as ``pypy_interact`` from other languages than Python,     
    to embed a sandboxed interpreter inside programs written in other           
    languages. 

To run the sandboxed process, you need to get the full sources and
build ``pypy-sandbox`` from it (see `Building from source`_).  These
instructions give you a ``pypy-c`` that you should rename to
``pypy-sandbox`` to avoid future confusion.  Then run:

.. code-block:: bash

    cd pypy/sandbox
    pypy_interact.py path/to/pypy-sandbox
    # don't confuse it with pypy/goal/pyinteractive.py!

You get a fully sandboxed interpreter, in its own filesystem hierarchy
(try ``os.listdir('/')``).  For example, you would run an untrusted
script as follows:

.. code-block:: bash

   mkdir virtualtmp
   cp untrusted.py virtualtmp/
   pypy_interact.py --tmp=virtualtmp pypy-sandbox /tmp/untrusted.py

Note that the path ``/tmp/untrusted.py`` is a path inside the sandboxed
filesystem.  You don't have to put ``untrusted.py`` in the real ``/tmp``
directory at all.

To read more about its features, try ``pypy_interact.py --help`` or go to
`our documentation site`_.

.. _`Building from source`: download.html#building-from-source
.. _`our documentation site`: http://pypy.readthedocs.org/en/latest/sandbox.html

.. _`contact us`: contact.html
.. _Prolog: https://github.com/cosmoharrigan/pyrolog
.. _Smalltalk: https://bitbucket-archive.softwareheritage.org/projects/py/pypy/lang-smalltalk.html
.. _JavaScript: https://bitbucket-archive.softwareheritage.org/projects/py/pypy/lang-js.html
.. _Io: https://bitbucket-archive.softwareheritage.org/projects/py/pypy/lang-io.html
.. _Scheme: https://bitbucket-archive.softwareheritage.org/projects/py/pypy/lang-scheme.html
.. _Gameboy: https://bitbucket-archive.softwareheritage.org/projects/py/pypy/lang-gameboy.html
.. _Topaz: https://github.com/topazproject/topaz
.. _HippyVM: http://www.hippyvm.com/
