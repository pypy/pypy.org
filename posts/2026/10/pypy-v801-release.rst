.. title: PyPy v8.0.1 release
.. slug: pypy-v801-release
.. date: 2026-09-14 08:00:00 UTC
.. tags: release
.. category: 
.. link: 
.. description: 
.. type: rst
.. author: mattip

===========================================================================
PyPy v8.0.1: release of python 2.7, 3.11, and 3.12 beta released 2026-09-14
===========================================================================

The PyPy team is proud to release version 8.0.1 of PyPy after the previous
release on Sept 25, 2026. Some problems with buffer memory leaks were fixed,
and problems around the new strategy to tie RPython objects to non-managed C
``PyObject`` objects were also fixed. The stdlib for 3.11 and 3.12 was updated,
as was the vendored libexpat (to 2.8.5). Internally, we now use pytest3.10
rather than 2.9.2.

The release includes three different interpreters:

- PyPy2.7, supporting the syntax and the features of
  Python 2.7 including the stdlib for CPython 2.7.18+ (the ``+`` is for
  backported security updates)

- PyPy3.11, supporting the syntax and the features of
  Python 3.11, including the stdlib for CPython 3.11.17. Barring security
  issues, this will be the last release to support 3.11.

- PyPy3.12, supporting the syntax and features of Python 3.12, including the
  stdlib for CPython 3.12.15.

The interpreters are based on much the same codebase, thus the triple
release.

We recommend updating. You can find links to download the releases here:

    https://pypy.org/download.html

We would like to thank our donors for the continued support of the PyPy
project. If PyPy is not quite good enough for your needs, we are available for
`direct consulting`_ work. If PyPy is helping you out, we would love to hear
about it and encourage submissions to our blog_ via a pull request
to https://github.com/pypy/pypy.org

We would also like to thank our contributors and encourage new people to join
the project. PyPy has many layers and we need help with all of them: bug fixes,
`PyPy`_ and `RPython`_ documentation improvements, or general `help`_ with
making RPython's JIT even better.

If you are a python library maintainer and use C-extensions, please consider
making a CFFI_ version of your library that would be performant
on PyPy. Failing that, PyPy will soon support the cp312-abi3 tag for limited
ABI wheels.  In any case, `cibuildwheel`_ supports building wheels for PyPy.

.. _`PyPy`: https://doc.pypy.org/
.. _`RPython`: https://rpython.readthedocs.org
.. _`help`: https://doc.pypy.org/project-ideas.html
.. _CFFI: https://cffi.readthedocs.io
.. _`cibuildwheel`: https://github.com/joerick/cibuildwheel
.. _blog: https://pypy.org/blog
.. _HPy: https://hpyproject.org/
.. _direct consulting: https://www.pypy.org/pypy-sponsors.html

What is PyPy?
=============

PyPy is a Python interpreter, a drop-in replacement for CPython.
It's fast (`PyPy and CPython`_ performance
comparison) due to its integrated tracing JIT compiler.

We also welcome developers of other `dynamic languages`_ to see what RPython
can do for them.

We provide binary builds for:

* **x86** machines on most common operating systems
  (Linux 32/64 bits, Mac OS 64 bits, Windows 64 bits)

* 64-bit **ARM** machines running Linux (``aarch64``) and macos (``macos_arm64``).

PyPy supports Windows 32-bit, Linux PPC64 big- and little-endian, Linux ARM
32 bit, RISC-V RV64IMAFD Linux, and s390x Linux but does not release binaries.
Please reach out to us if you wish to sponsor binary releases for those
platforms. Downstream packagers provide binary builds for debian, Fedora,
conda, OpenBSD, FreeBSD, Gentoo, and more.

.. _`PyPy and CPython`: https://speed.pypy.org
.. _`dynamic languages`: https://rpython.readthedocs.io/en/latest/examples.html

What else is new?
=================

For more information about the release, see the `full changelog`_.

Please update, and continue to help us make pypy better.

Cheers,
The PyPy Team

.. _`full changelog`: https://doc.pypy.org/en/latest/release-v8.0.1.html#changelog 
