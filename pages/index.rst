.. title: PyPy
.. slug: index
.. date: 2019-12-28 16:14:02 UTC
.. tags: 
.. category: 
.. link: 
.. description: 
.. type: text

.. raw:: html

    <div class="row">
    <div class="column pb-4">

.. image:: images/pypy-logo.svg
    :alt: PyPy logo
    :width: 350px

A `fast`_, `compliant`_ alternative implementation of `Python`_

.. raw:: html

    <a id="download" href="download.html">
        <img src="images/download.svg">
        Download PyPy
    </a>
    

.. class:: button

    `What is PyPy`_ : Features

.. class:: button

    `Documentation`_ (external link)

.. _`Get Started`: download.html
.. _`What is PyPy`: features.html
.. _`Documentation`: https://doc.pypy.org

.. raw:: html

    </div>
    <div class="column pb-4" "flex-basis: 400px">

.. class:: small

On average, PyPy is **4.2 times faster** than CPython

.. figure:: images/pypy_speed_graph.png
    :alt: PyPy vs. Python speed comparison graph"
    :figclass: text-sm

    PyPy trunk (with JIT) benchmark times normalized to CPython. Smaller is
    better. Based on the geometric average of all benchmarks

.. raw:: html

    </div>
    </div>

::

    "If you want your code to run faster,
    you should probably just use PyPy."
    -- Guido van Rossum (creator of Python)

**Advantages and distinct Features**

* **Speed:** thanks to its Just-in-Time compiler, Python programs
  often run `faster`_ on PyPy.  `(What is a JIT compiler?)`_

* **Memory usage:** memory-hungry Python programs (several hundreds of
  MBs or more) might end up taking `less space`_ than they do in CPython.

* **Compatibility:** PyPy is `highly compatible`_ with existing python code.
  It supports `cffi`_, `cppyy`_, and can run popular python libraries like
  `twisted`_ and `django`_.

* **Stackless:** PyPy comes by default with support for `stackless mode`_,
  providing micro-threads for massive concurrency.

* As well as other `features`_.

.. _`stackless mode`: features.html#stackless
.. _`Python`: http://python.org/
.. _`fast`: http://speed.pypy.org/
.. _`faster`: http://speed.pypy.org/
.. _`(What is a JIT compiler?)`: http://en.wikipedia.org/wiki/Just-in-time_compilation
.. _`run untrusted code`: features.html#sandboxing
.. _`compliant`: compat.html
.. _`Python docs`: http://docs.python.org/2.7
.. _`twisted`: https://twistedmatrix.com/
.. _`django`: https://www.djangoproject.com/
.. _`cffi`: https://cffi.readthedocs.org
.. _`cppyy`: https://cppyy.readthedocs.org
.. _`features`: features.html
.. _`less space`: http://morepypy.blogspot.com/2009/10/gc-improvements.html
.. _`highly compatible`: compat.html
.. _`speed`: http://speed.pypy.org/
.. _`compatibility`: compat.html
