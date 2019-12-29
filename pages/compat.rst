.. title: Python compatibility
.. slug: compat
.. date: 2019-12-28 16:14:02 UTC
.. tags: 
.. category: 
.. link: 
.. description: 

PyPy implements the Python language version 2.7.13. It supports all of the core
language, passing Python test suite (with minor modifications that were
already accepted in the main python in newer versions). It supports most
of the commonly used Python `standard library modules`_; details below.

PyPy3 implements the Python language version 3.6.9.  It has been released,
but Python is a large language and it is quite possible that a few things are missing.

.. class:: download_menu

   `List of installable top 1000 PyPI packages`_

PyPy has support for the `CPython C API`_, however there are constructs
that are `not compatible`.  We strongly advise use of `CFFI`_
instead. CFFI come builtin with PyPy. Many libraries will require
a bit of effort to work, but there are known success stories. Check out
PyPy blog for updates, as well as the `Compatibility Wiki`__.

.. __: https://bitbucket.org/pypy/compatibility/wiki/Home

C extensions need to be recompiled for PyPy in order to work. Depending on
your build system, it might work out of the box or will be slightly harder.

Standard library modules supported by PyPy. Note that large parts of python
library are implemented in pure python, so they don't have to be listed
there. Please just check if it imports. If it imports, it should work.

* ``__builtin__, __pypy__, _ast, _cffi_backend, _codecs, _collections, _continuation, _csv, _file, _hashlib, _io, _locale, _lsprof, _md5, _minimal_curses, _multibytecodec, _multiprocessing, _numpypy, _pickle_support, _pypyjson, _random, _rawffi, _sha, _socket, _sre, _ssl, _struct, _testing, _warnings, _weakref, array, binascii, bz2, cStringIO, cmath, cppyy, cpyext, crypt, errno, exceptions, fcntl, gc, imp, itertools, marshal, math, mmap, operator, parser, posix, pwd, pyexpat, pypyjit, select, signal, symbol, sys, termios, thread, time, token, unicodedata, zipimport, zlib``

Supported, but written in pure Python:

* ``cPickle, ctypes, datetime, dbm, _functools, grp, readline, resource, sqlite3, syslog``

All modules that are pure python in CPython of course work.

Python libraries known to work under PyPy (the list is not exhaustive).
A `fuller list`_ is available.

* ctypes

* django

* sqlalchemy

* flask

* twisted

* pylons

* divmod's nevow

* pyglet

* Pillow (the PIL fork)

* `lxml`_

* NumPy

The main difference that is not going to be fixed is that PyPy does
not support refcounting semantics. The following code won't fill the
file immediately, but only after a certain period of time, when the GC
does a collection:

.. code-block:: python

    open("filename", "w").write("stuff")

The proper fix is

.. code-block:: python

    f = open("filename", "w")
    f.write("stuff")
    f.close()

or using the ``with`` keyword

.. code-block:: python

    with open("filename", "w") as f:
        f.write("stuff")

The same problem---not closing your files---can also show up if your
program opens a large number of files without closing them explicitly.
In that case, you can easily hit the system limit on the number of file
descriptors that are allowed to be opened at the same time.

Since release 5.4, PyPy can be run with the command-line option ``-X
track-resources`` (as in, ``pypy -X track-resources myprogram.py``).
This produces a ResourceWarning when the GC closes a non-closed file or
socket.  The traceback for the place where the file or socket was
allocated is given as well, which aids finding places where ``close()``
is missing.

Similarly, remember that you must ``close()`` a non-exhausted
generator in order to have its pending ``finally`` or ``with``
clauses executed immediately:

.. code-block:: python

    def mygen():
        with foo:
            yield 42

    for x in mygen():
        if x == 42:
            break    # foo.__exit__ is not run immediately!

    # fixed version:
    gen = mygen()
    try:
        for x in gen:
            if x == 42:
                break
    finally:
        gen.close()

More generally, ``__del__()`` methods are not executed as predictively
as on CPython: they run "some time later" in PyPy (or not at all if
the program finishes running in the meantime).  See `more details
here`_.

Note that PyPy returns unused memory to the operating system if there
is a madvise() system call (at least Linux, OS X, BSD) or on Windows.  It is
important to realize that you may not see this in ``top``.  The unused
pages are marked with ``MADV_FREE``, which tells the system "if you
need more memory at some point, grab this page".  As long as memory is
plentiful, the ``RES`` column in ``top`` might remains high.  (Exceptions to
this rule are systems with no ``MADV_FREE``, where we use
``MADV_DONTNEED``, which forcefully lowers the ``RES``.  This includes
Linux <= 4.4.)

A more complete list of known differences is available at `our dev site`_.

.. _`CPython C API`: http://docs.python.org/c-api/
.. _`CFFI`: http://cffi.readthedocs.org/
.. _`not compatible`: http://doc.pypy.org/en/latest/cpython_differences.html#c-api-differences
.. _`standard library modules`: http://docs.python.org/library/
.. _`our dev site`: http://pypy.readthedocs.org/en/latest/cpython_differences.html
.. _`more details here`: http://pypy.readthedocs.org/en/latest/cpython_differences.html#differences-related-to-garbage-collection-strategies
.. _`compatibility wiki`: https://bitbucket.org/pypy/compatibility/wiki/Home
.. _`lxml`: https://github.com/amauryfa/lxml/tree/cffi/
.. _`List of installable top 1000 PyPI packages`: http://packages.pypy.org
.. _`fuller list`: http://packages.pypy.org
