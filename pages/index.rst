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

A `fast`_, `compliant`_ alternative implementation of `Python`_

.. raw:: html

    <a id="download" href="download.html">
        <img src="images/download.svg">
        Download PyPy
    </a>
    

.. class:: button

    `What is PyPy`_ ?

.. class:: button

    `Documentation`_ (external link)

.. _`Get Started`: download.html
.. _`What is PyPy`: features.html
.. _`Documentation`: https://doc.pypy.org


.. raw:: html

    </div>
    <div class="column pb-4"">

.. image:: images/pypy-logo.svg
    :alt: PyPy logo
    :width: 300px


.. raw:: html

    </div>
    </div>


.. class:: small

On average, PyPy is **about 3 times faster** than CPython 3.11. We currently support python 3.11 and 2.7.

.. figure:: images/pypy_speed_graph.png
    :alt: PyPy vs. Python speed comparison graph"
    :figclass: text-sm
    :width: 100%

    PyPy (with JIT) benchmark times normalized to CPython. Smaller is
    better. Based on the geometric average of all benchmarks

::

    "... we are avid fans of PyPy and
    commensurately thankful for the great work by the PyPy team over the
    years. PyPy has enabled us to use Python for a larger part of our
    toolset than CPython alone would have supported, and its smooth
    integration with C/C++ through CFFI has helped us attain a better
    tradeoff between performance and programmer productivity in our
    projects"
    -- Vilhjálmur Þorsteinsson, founder and CEO of Miðeind, Feb 2022

**Advantages and distinct Features**

* **Speed:** thanks to its Just-in-Time compiler, Python programs
  often run `faster`_ on PyPy.  `(What is a JIT compiler?)`_

* **Memory usage:** memory-hungry Python programs (several hundreds of
  MBs or more) might end up taking `less space`_ than they do in CPython.

* **Compatibility:** PyPy is `highly compatible`_ with existing python code.
  It supports `cffi`_, `cppyy`_, and can run popular python libraries like
  `twisted`_, and `django`_. It can also run NumPy, Scikit-learn and more via a
  c-extension compatibility layer.

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
.. _`Python docs`: http://docs.python.org/3
.. _`twisted`: https://twistedmatrix.com/
.. _`django`: https://www.djangoproject.com/
.. _`cffi`: https://cffi.readthedocs.org
.. _`cppyy`: https://cppyy.readthedocs.org
.. _`features`: features.html
.. _`less space`: /posts/2009/10/gc-improvements-6174120095428192954.html
.. _`highly compatible`: compat.html
.. _`speed`: http://speed.pypy.org/
.. _`compatibility`: compat.html
