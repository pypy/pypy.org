.. title: How is PyPy Tested?
.. slug: how-is-pypy-tested
.. date: 2022-04-02 15:00:00 UTC
.. tags:
.. category: 
.. link: 
.. description: 
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

===================
How is PyPy Tested?
===================

In this post I want to give an overview of how the PyPy project does and thinks
about testing. PyPy takes testing quite seriously and has done some from the
start of the project. Here I want to present the different styles of
tests that PyPy has, when we use them and how I think about them.


Background
============

To make the blog post self-contained, I am going to start with a small overview
about PyPy's architecture. If you already know what PyPy is and how it works,
you can skip this section.

PyPy means "Python in Python". It is an alternative implementation of the Python
language. Usually, when we speak of "Python", we can mean two different things.
On the one hand it means "Python as an abstract programming language". On the
other hand, the main implementation of that language is also often called
"Python". To more clearly distinguish the two, the implementation is often also
called "CPython", because it is an interpreter implemented in C code.

Now we can make the statement "PyPy is Python in Python" more precise: PyPy is
an interpreter for Python 3.9, implemented in RPython. RPython ("Restricted
Python") is a subset of Python 2, which is statically typed (using type
inference, not type annotations) and can be compiled
to C code. That means we can take our Python 3.9 interpreter, and compile it
into a C binary that can run Python 3.9 code. The final binary behaves pretty
similarly to CPython.

The main thing that makes PyPy interesting is that during the translation of our
interpreter to C, a number of components are automatically inserted into the
final binary. One component is a reasonably good garbage collector. 

The more exciting component that is inserted into the binary is a just-in-time
compiler. The insertion of this component is not fully automatic, instead it is
guided by a small number of annotations in the source code of the interpreter.
The effect of inserting this JIT compiler into the binary is that the resulting
binary can run Python code significantly faster than CPython, in many cases.
How this works is not important for the rest of the post, if you want to see an
example of concretely doing that to a small interpreter you can look at this
video_.

.. _video: https://www.youtube.com/watch?v=fZj3uljJl_k


PyPy Testing History
=====================

A few historical notes on the PyPy project and its relationship to testing: The
PyPy project `was started in 2004`_. At the time when the project was started,
Extreme Programming and Agile Software Development were up and coming. On the
methodology side, PyPy was heavily influenced by these, and started using
Test-Driven Development and pair programming right from the start.

.. _`was started in 2004`: https://www.pypy.org/posts/2018/09/the-first-15-years-of-pypy-3412615975376972020.html

Also technologically, PyPy has been influential on testing in the Python world.
Originally, PyPy had used the ``unittest`` testing framework, but pretty soon
the developers got frustrated with it. `Holger Krekel`_, one of the original
developers who started PyPy, started the pytest_ testing framework soon
afterwards.

.. _`Holger Krekel`: https://holgerkrekel.net/
.. _`pytest`: https://pytest.org/


Interpreter-Level Tests
=========================

So, how are tests for PyPy written, concretely? The tests for the interpreter
are split into two different kinds, which we call "interpreter level tests" and
"application level tests". The former are tests that can be used to test the
objects and functions that are used in the implementation of the Python
interpreter. Since the interpreter is written in Python 2, those tests are also
written in Python 2, using pytest. They tend to be more on the unit test side of
things. They are in files with the pattern ``test_*.py``.

Here is an example that tests the implementation of integers (very slightly
simplified):

.. code:: python

    class TestW_IntObject:
        ...

        def test_hash(self):
            w_x = W_IntObject(42)
            w_result = w_x.descr_hash(self.space)
            assert isinstance(w_result, W_IntObject)
            assert w_result.intval == 42


This test checks that if you take an object that represents integers in the
Python language (using the class ``W_IntObject``, a "wrapped integer object")
with the value 42, computing the hash of that object returns another instance of
the same class, also with the value 42.

These tests can be run on top of any Python 2 implementation, either CPython or
PyPy. We can then test and debug the internals of the PyPy interpreter using
familiar tools like indeed pytest and the Python debuggers. They can be run,
because all the involved code like the tests and the class ``W_IntObject`` are
just completely regular Python 2 classes that behave in the regular way when
run on top of a Python interpreter.

In CPython, these tests don't really have an equivalent. They would correspond
to tests that are written in C and that can test the logic of all the C
functions of CPython that execute certain functionality, accessing the internals
of C structs in the process. `¹`_


Application-Level Tests
=========================

There is also a second class of tests for the interpreter. Those are tests that
don't run on the level of the implementation. Instead, they are executed *by*
the PyPy Python interpreter, thus running on the level of the applications run
by PyPy. Since the interpreter is running Python 3, the tests are also written
in Python 3. They are stored in files with the pattern ``apptest_*.py`` and
look like "regular" Python 3 tests. `²`_

Here's an example of how you could write a test equivalent to the one above:

.. code:: python

    def test_hash():
        assert hash(42) == 42

This style of test looks more "natural" and is the preferred one in cases where
the test does not need to access the internals of the logic or the objects of
the interpreter.

Application level tests can be run in two different ways. On the one hand, we
can simply run them on CPython 3. This is very useful! Since we want PyPy to
behave like CPython, running the tests that we write on CPython is useful to
make sure that the tests themselves aren't wrong.

On the other hand, the main way to run these tests is on top of PyPy, itself
running on top of a Python 2 implementation. This makes it possible to run the
test without first bootstrapping PyPy to C. Since bootstrapping to C is a
relatively slow operation (can take up to an hour) it is crucially important to
be able to run tests without bootstrapping first. It also again makes it
possible to debug crashes in the interpreter using the regular Python 2
debugger. Of course running tests in this way is unfortunately itself not super
fast, given that they run on a stack of two different interpreters. 

Application-level tests correspond quite closely to CPython's tests suite (which
is using the unittest framework). Of course in CPython it is not possible to run
the test suite without building the CPython binary using a C compiler. `³`_

So when do we write application-level tests, and when interpreter-level tests?
Interpreter-level tests are necessary to test internal data structures that
touch data and logic that is not directly exposed to the Python language. If
that is not necessary, we try to write application-level tests. App-level tests
are however by their nature always more on the integration test side of things.
To be able to run the ``test_hash`` function above, many parts of PyPy need to
work correctly, the parser, the bytecode compiler, the bytecode interpreter, the
``hash`` builtin, calling the ``__hash__`` special method, etc, etc.

This observation is also true for CPython! One could argue that CPython has no
unit tests at all, because in order to be able to even run the tests, most of
Python needs to be in working order already, so all the tests are really
implicitly integration tests.


The CPython Test Suite
========================

We also use the CPython Test suite as a final check to see whether our
interpreter correctly implements all the features of the Python language. In
that sense it acts as some kind of compliance test suite that checks whether we
implement the language correctly. The test suite is not perfect for this.
Since it is written for CPython's purposes during its development, a
lot of the tests check really specific CPython implementation details. Examples
for these are tests that check that ``__del__`` is called immediately after
objects go out of scope (which only happens if you use reference counting as a
garbage collection strategy, PyPy uses a `different approach to garbage
collection`_). Other examples are checking
for exception error messages very explicitly. However, the CPython test suite
has gotten a lot better in these regards over time, by adding
``support.gc_collect()`` calls to fix the former problem, and by marking some
very specific tests with the ``@impl_detail`` decorator. Thanks to all the
CPython developers who have worked on this!

.. _`different approach to garbage collection`: https://www.pypy.org/posts/2013/10/incremental-garbage-collector-in-pypy-8956893523842234676.html

In the process of re-implementing CPython's functionality and running CPython's
tests suite, PyPy can often also be a good way to find bugs in CPython. While we
think about the corner cases of some Python feature we occasionally find
situations where CPython didn't get everything completely correct either, which
we then report back.


Testing for Performance Regressions
====================================

All the tests we described so far are checking *behaviour*. But one of PyPy's
important goals is to be a *fast* implementation not "just" a correct one. Some
aspects of performance can be tested by regular unit tests, either application-
or interpreter-level. In order to check whether some performance shortcut is
taken in the interpreter, we sometimes can write tests that monkeypatch the slow
default implementation to always error. Then, if the fast path is taken
properly, that slow default implementation is never reached.

But we also have additional tests that test the correct interaction with the JIT
explicitly. For that, we have a special style of test that checks that the JIT
will produce the correct machine code for a small snippet of Python code. To
make this kind of test somewhat more robust, we don't check the machine code
directly, but instead the architecture independent `intermediate
representation`_ that the JIT uses to produce machine code from.

.. _`intermediate representation`: https://www.pypy.org/posts/2018/09/the-first-15-years-of-pypy-3412615975376972020.html

As an example, here is a small test that loading the attribute of a constant
global instance can be completely constant folded away:

.. code:: python

    def test_load_attr(self):
        src = '''
            class A(object):
                pass
            a = A()
            a.x = 1
            def main(n):
                i = 0
                while i < n:
                    i = i + a.x
                return i
        '''
        log = self.run(src, [1000])
        assert log.result == 1000
        loop, = log.loops_by_filename(self.filepath)
        assert loop.match("""
            i9 = int_lt(i5, i6)
            guard_true(i9, descr=...)
            guard_not_invalidated(descr=...)
            i10 = int_add(i5, 1)
            --TICK--
            jump(..., descr=...)
        """)

The string passed to the ``loop.match`` function is a string representation of
the intermediate representation code that is generated for the ``while`` loop in
the ``main`` function given in the source. The important part of that
intermediate representation is that the ``i = i + a.x`` addition is optimized
into an ``int_add(x, 1)`` operation. The second argument for the addition is the
constant ``1``, because the JIT noted that the global ``a`` is a constant, and
the attribute ``x`` of that instance is always ``1``. The test thus checks that
this optimization still works.

Those tests are again more on the unit test side of things (and can thus
unfortunately be a bit brittle sometimes and break). The integration test
equivalent for performance is the `PyPy Speed Center`_ which tracks the
performance of micro- and macro-benchmarks over time and lets us see when big
performance regressions are happening. The speed center is not really an
automatic test and does not produce pass/fail outcomes. Instead, it requires
human judgement and intervention in order to interpret the performance changes.
Having a real pass/fail mechanism is something that would be `great to have`_
but is probably `quite tricky in practice`_.

.. _`great to have`: https://twitter.com/glyph/status/1495122754286198790
.. _`quite tricky in practice`: https://arxiv.org/abs/1602.00602

.. _`PyPy Speed Center`: https://speed.pypy.org/


Conclusion
===========

This concludes my overview of some of the different styles of tests that we use
to develop the PyPy Python interpreter.

There is a whole other set of tests for the development of the RPython language,
the garbage collectors it provides as well as the code that does the automatic
JIT insertion, maybe I'll cover these in a future post.


Footnotes
-----------

.. _`¹`:

¹ CPython has the `_testcapimodule.c` and related modules, that are used to
unit-test the C-API. However, these are still driven from Python tests using
the ``unittest`` framework and wouldn't run without the Python interpreter
already working.


.. _`²`:

² There is also a deprecated different way to write these tests, by putting
them in the ``test_*.py`` files that interpreter level tests are using and
then having a test class with the pattern ``class AppTest*``. We haven't
converted all of them to the new style yet, even though the old style is
quite weird: since the ``test_*.py`` files are themselves parsed by
Python 2, the tests methods in ``AppTest*`` classes need to be written in the
subset of Python 3 syntax that is also valid Python 2 syntax, leading to a lot
of confusion.

.. _`³`:

³ Nit-picky side-note: `C interpreters`_ `are a thing`_! But not that
widely used in practice, or only in very specific situations.

.. _`C interpreters`: https://root.cern.ch/root/html534/guides/users-guide/CINT.html
.. _`are a thing`: https://www.youtube.com/watch?v=yyDD_KRdQQU

