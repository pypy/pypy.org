.. title: Finding JIT Optimizer Bugs using SMT Solvers and Fuzzing
.. slug: jit-bug-finding-smt-fuzzing
.. date: 2022-12-30 15:00:00 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

In this blog post I want to describe a recent bug finding technique that I've
added to the PyPy JIT using the Z3 theorem prover. It's based on things I have
read John Regehr talk about on Twitter, and on his (et al) paper `Alive2:
Bounded Translation Validation for LLVM`__ and it was triggered by a recent
miscompilation bug my current bachelor student Nico Rittinghaus found.

.. __: https://www.cs.utah.edu/~regehr/alive2-pldi21.pdf

Background: Bounds Analysis in the JIT
======================================

The optimizer of PyPy's JIT has an analysis based on abstract interpretation
that tries to find out, whether the integer values stored in a variable are
actually not using the full 64 bit (or 32 bit) range, but instead fit into some
smaller range. This means that for every integer variable ``x`` in a trace, the JIT
compile tracks a range ``[a, b]`` with concrete integers ``a <= b`` in such a
way, that the for every concrete runtime execution of the trace with a concrete
value stored in ``x``, ``a <= x <= b`` must be true. ``a`` and ``b`` start out
as ``MININT`` and ``MAXINT``, but sometimes there is extra information that
makes it possible to improve these known bounds, and that is often useful to
optimize the code.

A typical example is that the JIT knows that the length of a string is
non-negative, so for this kind of code: ``x = len(s)`` where ``s`` is a string,
``x`` gets a range ``[0, MAXINT]`` assigned. With this information we could for
example remove a check ``x + 10 < 0`` completely, because it can never be True.

The bounds information is very useful for optimization, but the analysis of the
bounds is also a source of bugs in the JIT, because the reasoning is often
subtle and easy to get wrong in corner cases. We already use a number of testing
techniques to try to make sure that it is correct. A simple one is
property-based testing on the operations on bounds.

Motivation: A JIT Miscompilation
=================================

I am currently supervising a Bachelor thesis by Nico Rittinghaus, which is
extending the integer analysis in the JIT. He'll probably write a separate blog
post about it soon. In the process of doing that, the current bounds analysis
code got a lot of scrutiny, and we found out that one of the unit tests of the
bounds analysis was actually incorrect, and the example code in that unit test
was optimized incorrectly. This case of incorrect optimization is not a big deal
for regular Python code, because it involved a "wrapping integer addition
operation", i.e. one where overflowing results just wrap around to negative
values. In Python, all additions actually have overflow checks and convert to
a big integer representation if the results don't fit into a machine word.
However, it's still possible to trigger the problem with the the special
``__pypy__.intop.int_add`` API which is a function that exposes wraparound
arithmetic on ints.

Here's the miscompilation. The JIT optimizes the following function:

https://foss.heptapod.net/pypy/pypy/-/issues/3832


.. code:: python

    import __pypy__

    def wrong(x):
        a = __pypy__.intop.int_add(x, 10)
        if a < 15:
            if x < 6:
                return 0
            return 1
        return 2

Into the following code:

.. code:: python

    import __pypy__

    def wrong(x):
        a = __pypy__.intop.int_add(x, 10)
        if a < 15:
            return 0
        return 2

Basically the faulty reasoning of the JIT looks like this: if ``x + 10 < 15``
then it must follow that ``x < 5``, which is stronger than ``x < 6``, so the
second ``if`` is always True. This sounds good, but is of course actually wrong
if the addition ``+ 10`` overflowed. So if ``x == MAXINT``, then ``x + 10 ==
MININT + 9 < 15``. But ``MAXINT < 5`` is of course not correct.

Note how the same reasoning with overflow-checking addition is correct! And if
your brain bends starting to think about this, you understand some of the
difficulty of getting the JIT correct in this area.

How could we have avoided this bug?
=====================================

- thinking more carefully!
- bad API
- systematic approach: second source of truth about behaviour, SMT solving

Alive2: 

https://www.cs.utah.edu/~regehr/alive2-pldi21.pdf
https://github.com/AliveToolkit/alive2/

SMT Checking of the JIT Opimizer
==================================

- check that unoptimized and optimized versions of a trace behave identically

- steps:

  - align traces
  - use shared input variables for both versions of the trace
  - translate every operation
  - check that guard conditions have to compute the same results (using the not trick)
  - if a guard gets optimized away, it must always be true
  - result at the end must be the same

- apply this to all unit tests


Z3: https://github.com/Z3Prover/z3

Generating Random Traces
=========================

- try to find more bugs by generating random traces
- we already had a trace generator, to test the machine code backends!
- particularly the register allocator

- adopt it for the optimizer too

- neat trick: generate only possible traces by always having a concrete value
  for every variable in the trace, so that generated guards are always possible

- kind of the inverse of SMT

- run for a long time (probably by far not long enough yet!)


Bugs Found
============

- re-find the bug from the intro
- another one about integer negation that I had found by hand soon afterwards
- a bunch of crashes
- a real new bug, identified by Z3! incorrect CSE

- future things to do:
    - also mutate existing handwritten tests
    - extend for more operations (particularly the heap ops)
    - run much longer
    - some whitebox fuzzing maybe?
    - switch away from Z3 API and use smtlib2

- will probably find more once we add the new optimization
- good tool in the toolbox
