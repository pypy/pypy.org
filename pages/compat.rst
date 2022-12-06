.. title: Python compatibility
.. slug: compat
.. date: 2019-12-28 16:14:02 UTC
.. tags: 
.. category: 
.. link: 
.. description: 

The goal of this page is to point out some of the differences between running
python with PyPy and with CPython

TL;DR
-----

Pure python code works, but there are a few differences with object lifetime
management. Modules that use the `CPython C API`_ will probably work, but will
not achieve a speedup via the JIT. We encourage library authors to use `CFFI`_
and HPy_ instead.

If you are looking for how to use PyPy with the scientific python ecosystem,
we encourage you to use `conda`_, since they repackage common libraries like
scikit-learn and SciPy for PyPy.

Refcounting, ``__del__``, and resource use
------------------------------------------

The main difference in pure-python code that is not going to be fixed is that
PyPy does
not support refcounting semantics for "automatically" releasing state when
an object's ``__del__`` is called. The following code won't fill the
file immediately, but only after a certain period of time, when the GC
does a collection and flushes the output, since the file is only closed when
the ``__del__`` method is called:

.. code-block:: python

    open("filename", "w").write("stuff")

The proper fix is

.. code-block:: python

    with open("filename", "w") as f:
        f.write("stuff")

The same problem---not closing your files---can also show up if your
program opens a large number of files without closing them explicitly.
In that case, you can easily hit the system limit on the number of file
descriptors that are allowed to be opened at the same time.

PyPy can be run with the command-line option ``-X track-resources`` (as in,
``pypy -X track-resources myprogram.py``). This produces a ``ResourceWarning``
when the GC closes a non-closed file or socket.  The traceback for the place
where the file or socket was allocated is given as well, which aids finding
places where ``close()`` is missing.

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

Why is memory usage so high?
----------------------------

Note that PyPy returns unused memory to the operating system only after
a madvise() system call (at least Linux, OS X, BSD) or on Windows.  It is
important to realize that you may not see this in ``top``.  The unused
pages are marked with ``MADV_FREE``, which tells the system "if you
need more memory at some point, grab this page".  As long as memory is
plentiful, the ``RES`` column in ``top`` might remains high.  (Exceptions to
this rule are systems with no ``MADV_FREE``, where we use
``MADV_DONTNEED``, which forcefully lowers the ``RES``.  This includes
Linux <= 4.4.)

More info
---------

A more complete list of known differences is available at `our dev site`_.

.. _`CPython C API`: http://docs.python.org/c-api/
.. _`CFFI`: http://cffi.readthedocs.org/
.. _HPy: https://hpyproject.org/
.. _`conda`: https://conda-forge.org/blog/posts/2020-03-10-pypy/
.. _`our dev site`: http://pypy.readthedocs.org/en/latest/cpython_differences.html
.. _`more details here`: http://pypy.readthedocs.org/en/latest/cpython_differences.html#differences-related-to-garbage-collection-strategies
