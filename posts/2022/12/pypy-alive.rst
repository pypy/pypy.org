.. title: Finding JIT Optimizer Bugs using SMT Solvers and Fuzzing
.. slug: jit-bug-finding-smt-fuzzing
.. date: 2022-12-11 18:00:00 UTC
.. tags: jit, testing, z3
.. category:
.. link:
.. description:
.. type: rest
.. author: CF Bolz-Tereick

In this blog post I want to describe a recent bug finding technique that I've
added to the PyPy JIT testing infrastructure. This technique uses the Z3
theorem prover to find bugs in the optimizer of PyPy's JIT, in particular its
integer operation optimizations. The approach is
based on things I have learned from `John Regehr's`_ blog_ (`this post`_ is a
good first one to read), Twitter_, and on
his (et al) paper `Alive2: Bounded Translation Validation for LLVM`__. The work
was triggered by a recent miscompilation bug my current bachelor student Nico
Rittinghaus found.

.. _`John Regehr's`: https://www.cs.utah.edu/~regehr/
.. _blog: https://blog.regehr.org/
.. _`this post`: https://blog.regehr.org/archives/1122
.. _Twitter: https://twitter.com/johnregehr/
.. __: https://www.cs.utah.edu/~regehr/alive2-pldi21.pdf

Background: Python Integers in the PyPy JIT
=============================================

The optimizer of PyPy's JITs operates on traces, which are linear sequences of
instructions with guards. The instructions in the traces operate on different
machine-level data types, machine integers, doubles, pointers, bools, etc. In
this post we'll be mostly concerned with machine integers.

To given some wider context I'll explain a bit how Python ints in the user code
relate to the types that are used in traces when the PyPy Python implementation
is used.
When PyPy turns a regular Python 3 function into a trace, there is a lot of work
happening in the JIT frontend to try to observe and infer the types that the
Python function concretely uses at runtime. The traces are generated under these
typing assumptions. Therefore, code that uses ``ints`` in the Python code can
typically be translated into traces that operate on machine integers. In order
to make sure that the Python integer semantics are upheld, many of the
operations in the traces need to check that the integer results of some
operations still fit into a machine integer. If that is not the case (a rare
situation for most programs), the trace is left via a guard, execution falls
back to the interpreter, and there a big integer representation is chosen for
the too big value (the big integer representation is done via a pointer and
some storage on the heap).

All of this machinery is not going to be too relevant for the rest of the
post. For the post it's important to know that trace instructions operate on
machine integers and other low-level types, and some of the operations can
optionally check whether the
results still fit into a machine integer. These trace operations are improved by
the optimizer, which tries to transform the trace into one that behaves the
same, but is less costly to execute.


Background: Bounds Analysis in PyPy's JIT
==========================================

The optimizer of PyPy's JIT has an analysis based on `abstract interpretation`_
that tries to find out whether the integer values stored in a variable are
actually not using the full 64 bit (or 32 bit) range, but instead fit into some
smaller range. This means that for every integer variable ``x`` in a trace, the
JIT compiler tracks upper and lower bounds of the runtime value of that
variable: a range ``[a, b]`` such that for every concrete runtime value ``v``
that gets stored in variable ``x``, ``a <= v <= b`` must be true.
``a`` and ``b`` start out
as the most general ``MININT`` and ``MAXINT``, but sometimes there is extra
information that makes it possible to improve these known bounds, and that is
often useful to optimize the code.

A typical example is that the JIT knows that the length of a string is
non-negative, so for this kind of code: ``x = len(s)`` where ``s`` is a string,
``x`` gets a range ``[0, MAXINT]`` assigned. With this information we could for
example remove a check ``x + 10 < 0`` completely, because it can never be true.

The bounds information is useful for optimization, but the analysis of the
bounds is also a source of bugs in the JIT, because the reasoning is often
subtle and easy to get wrong in corner cases. We already use a number of testing
techniques to try to make sure that it is correct. A simple one is
`property-based testing`_ using Hypothesis_ on the operations on bounds. Even
though Hypothesis is fantastic, it unfortunately does not catch
absolutely all the bugs even if we'd like it too, as we'll see in the next
section.

.. _`abstract interpretation`: https://en.wikipedia.org/wiki/Abstract_interpretation
.. _`property-based testing`: https://hypothesis.works/articles/what-is-property-based-testing/
.. _Hypothesis: https://github.com/HypothesisWorks/hypothesis

Motivation: A JIT Miscompilation
=================================

I am currently supervising a Bachelor thesis by Nico Rittinghaus, who is
extending the integer analysis in the JIT. He'll probably write a separate blog
post about that soon. In the process of his work, the current bounds analysis
code got a lot of scrutiny, and we found out that one of the unit tests of the
bounds analysis was actually incorrect, and the example code in that unit test
was optimized incorrectly. This case of incorrect optimization is not a big deal
for regular Python code, because it involved a "wrapping integer addition
operation", i.e. one where overflowing results just wrap around to negative
values. All the additions and other arithmetic operations that the PyPy Python
frontend generates actually have
overflow checks (to be able to switch to a big integer representation if
needed).
However, it's still possible to trigger the problem with the
``__pypy__.intop.int_add`` API which is a function that exposes wraparound
arithmetic on Python ints.

`Here's the miscompilation`_. The JIT optimizes the following function:

.. _`Here's the miscompilation`: https://foss.heptapod.net/pypy/pypy/-/issues/3832


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

Basically the faulty reasoning of the JIT looks like this: if ``int_add(x, 10) < 15``
then it must follow that ``x < 5``, which is stronger than ``x < 6``, so the
second ``if`` is always true. This sounds good, but is actually wrong
if the addition ``+ 10`` wrapped around. So if ``x == MAXINT``, then
``int_add(x, 10) == MININT + 9 < 15``. But ``MAXINT < 5`` is not
correct.

Note how the same reasoning with overflow-checking addition is correct! If ``x +
10 < 15`` and the ``+`` didn't overflow, then indeed ``x < 6``. And if your
mind bends starting to think about all this, you understand some of the
difficulty of getting the JIT correct in this area.

How could we have avoided this bug?
=====================================

One `exercise I try to do after finding bugs`_ is to reflect on ways that the
bug could have been avoided. I think this is particularly important in the JIT,
where bugs are potentially really annoying to find and can cause very strange
behaviour in basically arbitrary Python code.

It's easy to always answer this question with "try to think more carefully
when working", but that approach cannot be relied on in complicated situations,
because humans don't concentrate perfectly for long stretches of time.

A situation-specific problem I identified was the bad design of the range analysis API.
A range is not just represented by two numbers, instead it's two numbers
and two bools that are supposed to represent that some operation did or did not
underflow/overflow. The meaning of these bools was quite hard to grasp and easy
to get wrong, so probably they should never have been introduced in the first
place (and my bugfix indeed removed them).

But in the rest of this blog post I want to talk about another, systematic
approach that can be applied to the problem of mis-optimizations of integer
operations, and that is done by applying an SMT solver to the problem.

An SMT solver (`Satisfyability Modulo Theories`_) is a tool that can be used to
find out whether mathematical formulas are "satisfiable", i.e. whether
some chosen set of inputs exists that will make the formulas evaluate to true. SMT solvers are
commonly used in a wide range of CS applications including program correctness
proofs, program synthesis, etc. The most widely known one is probably Z3_ by
Microsoft Research which has the nice advantage of coming with an easy-to-use
Python binding.

Going into this I basically knew next to nothing about SMT solvers (despite
having been embedded in a formal methods research group for years!) so it was an
interesting new world to learn about.

.. _`exercise I try to do after finding bugs`: https://twitter.com/cfbolz/status/1482649144099586051
.. _`Satisfyability Modulo Theories`: https://en.wikipedia.org/wiki/Satisfiability_modulo_theories
.. _Z3: https://github.com/Z3Prover

As briefly mentioned in the introduction, the approach I took followed a similar
(but *much* more properly executed) one applied to LLVM operations, called
Alive2__. Krister Waldfridsson has done `similar work for GCC recently`__,
described on his blog.

.. __: https://github.com/AliveToolkit/alive2/
.. __: https://kristerw.github.io/2022/09/13/translation-validation/


Z3 Proof of Concept
=======================

The first thing I did was to try to get Z3 find the above bug, by encoding the
input program into an SMT formula by hand and trying to get Z3 to prove the condition
that the JIT thinks is always true. The Z3 code for this looks as follows:

.. code:: python

    from z3 import BitVec, Implies, prove
    x = BitVec('x', 64)
    a = x + 10
    cond1 = a < 15
    cond2 = x < 6
    prove(Implies(cond1, cond2))


Here, ``x`` is defined to be a bit vector variable of width 64, which is a
datatype that can be used to represent bounded machine integers. Addition on
bit vectors performs wraparound arithmetic, like the ``__pypy__.intop.int_add``
call in the original code. The JIT optimized the second condition away, so
essentially it was convinced that the first condition implies the second one.
The above snippet tries to get Z3 to confirm this.

When run, the above program prints::

    counterexample
    [x = 9223372036854775803]

Which shows the bug. As a small side-note, I thought it was cool that the
process of "proving" something in Z3 basically means trying to find an example
for the negation of the formula. If no counterexample can be found for the
negation, the original formula is true. If the original formula turns out to be
false (like here) we get a nice example that shows the problem to go with it.

It's not realistic to hand-translate all the hundreds of
unit-tests into Z3 formulas and then ask Z3 to prove the optimizations. Instead,
we want to have a program that does this for us.

SMT Checking of the JIT Optimizer
==================================

What we want from this program is the following: given an unoptimized trace and
its optimized version, we want to use Z3 to check whether the optimized trace
behaves identically to the unoptimized one. One question is what "behaves
identically" means. What we care about is the outputs of the trace being the
same values, no matter how they are computed. Also, for every guard we want to
make sure that it fails in identical ways in the optimized and unoptimized
versions. A guard is only allowed to be optimized away if it can never fail.
The code that comes after a guard can assume that the guard has not failed,
because otherwise execution would have left the trace. All of this should be
true regardless for the values of the input variables of the trace.

So in order to check that the two traces are behaving identically, we do the
following:

- We create Z3 variables for every input variable. We use the same input
  variables both for the unoptimized as well as the optimized trace.

- We align the two traces at the corresponding guards. Thankfully the optimizer
  keeps track of which optimized guard corresponds to which unoptimized input
  guard.

- All the operations before a guard are translated into Z3 formulas, for both
  versions of the trace.

- For two corresponding guards, we ask Z3 to prove that the guard conditions are
  identical.

- For a guard that was optimized away we ask Z3 to prove that the condition is
  always true.

- After a guard, we tell Z3 that from now on it can assume that the guard
  condition is true.

- We repeat this, guard for guard, until we reach the end of the trace. There,
  we ask Z3 to prove that the output variables in the unoptimized trace and the
  optimized trace are identical (every trace can return one or many values).

I implemented this, it's `not a lot of code`__, basically a couple of hundred lines
of (somewhat hacky) Python code. So far I only support integer
operations. Here are some parts of the code to give you a flavor of what this
looks like.

.. __: https://foss.heptapod.net/pypy/pypy/-/blob/branch/default/rpython/jit/metainterp/optimizeopt/test/test_z3checktests.py

This is the code that translates operations into Z3 formulas:

.. code:: python

    def add_to_solver(self, ops, state):
        for op in ops:
            if op.type != 'v': # is it an operation with a result
                res = self.newvar(op)
            else: # or does it return void
                res = None

           # ...

            # convert arguments
            if op.numargs() == 1:
                arg0 = self.convertarg(op, 0)
            elif op.numargs() == 2:
                arg0 = self.convertarg(op, 0)
                arg1 = self.convertarg(op, 1)

            # compute results
            if opname == "int_add":
                expr = arg0 + arg1
            elif opname == "int_sub":
                expr = arg0 - arg1
            elif opname == "int_mul":
                expr = arg0 * arg1
            elif opname == "int_and":
                expr = arg0 & arg1
            elif opname == "int_or":
                expr = arg0 | arg1
            elif opname == "int_xor":
                expr = arg0 ^ arg1

            # ...  more operations, some shown below

            self.solver.add(res == expr)


New Z3 variables are defined by the helper function ``newvar``, which adds the
operation to a dictionary ``box_to_z3`` mapping boxes (=variables) to Z3
variables. Due to the SSA_ property that traces have, a variable must be defined
before its first use.

Here's what ``newvar`` looks like (``LONG_BIT`` is a constant that is either
``64`` or ``32``, depending on the target architecture):

.. code:: python

    def newvar(self, box, repr=None):
        # ... some logic around making the string representation
        # somewhat nicer omitted
        result = z3.BitVec(repr, LONG_BIT)
        self.box_to_z3[box] = result
        return result

The ``convert`` method turns an operation argument (either a constant or a
variable) into a Z3 formula (either a constant bit vector or an already defined
Z3 variable). ``convertarg`` is a helper function that takes an operation, reads
its nth argument and converts it.

.. code:: python

    def convert(self, box):
        if isinstance(box, ConstInt):
            return z3.BitVecVal(box.getint(), LONG_BIT)
        return self.box_to_z3[box]

    def convertarg(self, box, arg):
        return self.convert(box.getarg(arg))

The lookup of variables in ``box_to_z3`` that ``convert`` does cannot fail,
because the variable must have been defined before use.


.. _SSA: https://en.wikipedia.org/wiki/Static_single-assignment_form

Comparisons return the bit vector 0 or bit vector 1, we use a helper function
``cond`` to turn the Z3 truth value of the comparison into a bit vector:


.. code:: python

    def cond(self, z3expr):
        return z3.If(z3expr, TRUEBV, FALSEBV)


    def add_to_solver(self, ops, state):
            # ... start as above

            # more cases
            elif opname == "int_eq":
                expr = self.cond(arg0 == arg1)
            elif opname == "int_ne":
                expr = self.cond(arg0 != arg1)
            elif opname == "int_lt":
                expr = self.cond(arg0 < arg1)
            elif opname == "int_le":
                expr = self.cond(arg0 <= arg1)
            elif opname == "int_gt":
                expr = self.cond(arg0 > arg1)
            elif opname == "int_ge":
                expr = self.cond(arg0 >= arg1)
            elif opname == "int_is_true":
                expr = self.cond(arg0 != FALSEBV)
            elif opname == "uint_lt":
                expr = self.cond(z3.ULT(arg0, arg1))
            elif opname == "uint_le":
                expr = self.cond(z3.ULE(arg0, arg1))
            elif opname == "uint_gt":
                expr = self.cond(z3.UGT(arg0, arg1))
            elif opname == "uint_ge":
                expr = self.cond(z3.UGE(arg0, arg1))
            elif opname == "int_is_zero":
                expr = self.cond(arg0 == FALSEBV)

            # ... rest as above

So basically for every trace operation that operates on integers I had to give a
translation into Z3 formulas, which is mostly straightforward.

Guard operations get converted into a Z3 boolean by their own helper function,
which looks like this:

.. code:: python

    def guard_to_condition(self, guard, state):
        opname = guard.getopname()
        if opname == "guard_true":
            return self.convertarg(guard, 0) == TRUEBV
        elif opname == "guard_false":
            return self.convertarg(guard, 0) == FALSEBV
        elif opname == "guard_value":
            return self.convertarg(guard, 0) == self.convertarg(guard, 1)

        # ... some more exist, shown below

Some operations are a bit trickier. An important example in the context of
this blog post are integer operations that check for overflow. The overflow
operations return a result, but also a boolean whether the operation overflowed
or not.

.. code:: python

    def add_to_solver(self, ops, state):

            # ... more cases

            elif opname == "int_add_ovf":
                expr = arg0 + arg1
                m = z3.SignExt(LONG_BIT, arg0) + z3.SignExt(LONG_BIT, arg1)
                state.no_ovf = m == z3.SignExt(LONG_BIT, expr)
            elif opname == "int_sub_ovf":
                expr = arg0 - arg1
                m = z3.SignExt(LONG_BIT, arg0) - z3.SignExt(LONG_BIT, arg1)
                state.no_ovf = m == z3.SignExt(LONG_BIT, expr)
            elif opname == "int_mul_ovf":
                expr = arg0 * arg1
                m = z3.SignExt(LONG_BIT, arg0) * z3.SignExt(LONG_BIT, arg1)
                state.no_ovf = m == z3.SignExt(LONG_BIT, expr)

            # ...

The boolean is computed by comparing the result of the bit vector operation with
the result of converting the input bit vectors into an abstract (arbitrary
precision) integer and the result back to bit vectors. Let's go through the
addition case step by step, the other cases work analogously.

The addition in the first ``elif`` that computes ``expr`` is an addition on bit
vectors, therefore it is performing wraparound arithmetic.
``z3.SignExt(LONG_BIT, arg0)`` sign-extends ``arg0`` from a bit vector of
``LONG_BIT`` bits to an abstract, arbitrary precision integer. The addition in
the second line is therefore an addition between abstract integers, so it will
never overflow and just compute the correct result as an integer.

The condition to check for overflow is now: if the results of the two different
ways to do the addition are the same, then overflow did not occur. So in order
to compute ``state.no_ovf`` in the addition case the
code converts the result of the bit vector wraparound addition to
an abstract integer (using ``SignExt`` again), and then compares that to the integer
result.

This boolean can then be checked by the guard operations ``guard_no_overflow``
and ``guard_overflow``.

.. code:: python

    def guard_to_condition(self, guard, state):

        # ... more cases

        elif opname == "guard_no_overflow":
            assert state.no_ovf is not None
            return state.no_ovf
        elif opname == "guard_overflow":
            assert state.no_ovf is not None
            return z3.Not(state.no_ovf)

        # ... more cases


Finding the Bug, Again
=======================

Let's actually make all of this more concrete by applying it to the trace of our
original bug. The input trace and the incorrectly optimized trace for that look
like this (differences highlighted):

.. code:: python
    :emphasize-lines: 6-8

    # input                       # optimized
    [i0]                          [i0]
    i1 = int_add(i0, 10)          i1 = int_add(i0, 10)
    i2 = int_lt(i1, 15)           i2 = int_lt(i1, 15)
    guard_true(i2)                guard_true(i2)
    i3 = int_lt(i0, 6)            jump(0)
    guard_true(i3)
    jump(0)

Note that the trace represents just one of the paths through the control flow
graph of the original function, which is typical for tracing JITs (the other
paths could incrementally get added later).

The first guards in both these traces correspond to each other, so the first
chunks to check are the first three operations (lines 1-4). Those operations
don't get changed by the optimizer at all.

These two identical traces get translated to the following Z3 formulas:

.. code::

    i1unoptimized == input_i0 + 10
    i2unoptimized == If(i1unoptimized < 15, 1, 0)
    i1optimized == input_i0 + 10
    i2optimized == If(i1optimized < 15, 1, 0)

To check that the two corresponding guards are the same, the solver is asked to
prove that ``(i2unoptimized == 1) == (i2optimized == 1)``. This is
correct, because the formulas for ``i2unoptimized`` and ``i2optimized`` are
completely identical.

After checking that the guards behave the same, we add the knowledge to the
solver that the guards passed. So the Z3 formulas become:

.. code::

    i1unoptimized == input_i0 + 10
    i2unoptimized == If(i1unoptimized < 15, 1, 0)
    i1optimized == input_i0 + 10
    i2optimized == If(i1optimized < 15, 1, 0)
    i1optimized == 1
    i2optimized == 1

Now we continue with the remaining operations of the two traces (lines 6-8).

We start by adding the ``int_lt`` operation in the unoptimized trace to the Z3
formulas:

.. code::

    ...
    i3unoptimized == If(input_i0 < 6, 1, 0)

Because the second guard was optimized away, we need to ask Z3 to prove that
``i3unoptimized == 1`` is always true, which fails and gives the following
counterexample:

.. code::

    input_i0 = 9223372036854775800
    i1unoptimized = 9223372036854775810
    i2unoptimized = 0
    i1optimized = 9223372036854775810
    i2optimized = 1
    i3unoptimized = 0

Thus demonstrating the bug. The fact that the Z3-based equivalence check also
managed to find the original motivating bug without manually translating it to
a formula is a good confirmation that the approach works.

Second bug
===========

So with this code I applied the Z3-based equivalence check to all our optimizer
unit tests. In addition to the bug we've been discussing the whole post, it also
found another buggy test! I had found it too by hand by staring at all the tests
in the process of writing all the Z3 infrastructure, but it was still a good
confirmation that the process worked. This bug was in the range analysis for
``int_neg``, integer negation. It failed to account that ``-MININT == MININT``
and therefore did a mis-optimization along the following lines:

.. code:: python

    import __pypy__

    def wrong(x):
        a = __pypy__.intop.int_sub(0, x)
        if a < 0:
            if x > 0:
                return 0
            return 1
        return 2

Which was wrongly optimized into:


.. code:: python

    import __pypy__

    def wrong(x):
        a = __pypy__.intop.int_sub(0, x)
        if a < 0:
            return 0
        return 2

This is wrong precisely for ``x == MININT``.

Generating Random Traces
=========================

These two bugs were the only two that the Z3 checker found for existing unit
tests. To try to find some more bugs I combined PyPy's existing random trace
generator with the Z3 optimization checker. The random trace generator has so
far been mostly used to find bugs in the machine code backends, particularly
also in the register allocator. So far we haven't used it with our optimizer,
but my experiments show that we should have!

I'm going to describe a little bit how the random trace generator works. It's
actually not that complicated, but there's one neat trick to it.

The basic idea is straightforward, it starts out with an empty trace with a
random number of input variables. Then it adds some number of operations to the
trace, either regular operations or guards. Every operation takes already
existing variables as input.

The neat trick is that our random trace generator keeps a concrete random
example value for every one of the input variables, and an example result for
every operation. In this way, it is possible to generate guards that are
consistent with the example values to ensure that running the trace to its end
is possible with at least one set of values.

Here's an example random trace that is generated, together with the random
example inputs and the results of every operation at the end of every line::

    [i0, i1, i2, i3, i4, i5] # example values: 9, 11, -8, -95, 46, 57
    i6 = int_add_ovf(i3, i0) # -86
    guard_no_overflow()
    i7 = int_sub(i2, -35/ci) # 27
    i8 = uint_ge(i3, i5) # 1
    guard_true(i8)
    i9 = int_lt(i7, i8) # 0
    i10 = int_mul_ovf(34/ci, i7) # 918
    guard_no_overflow()
    i11 = int_and(i10, 63/ci) # 22
    i12 = int_rshift(i3, i11) # -1
    i13 = int_is_zero(i7) # 0
    i14 = int_is_true(i13) # 0
    guard_false(i13)
    i15 = int_lt(i8, i4) # 1
    i16 = int_and(i6, i0) # 8
    i17 = uint_ge(i6, -6/ci) # 0
    finish()

Note how every guard generated is true for the example values.

I have been running this combination of random trace generation and Z3 checking
for many nights and it has found some bugs, which I'll describe in the next
section. It should probably be run for a lot longer, but still a useful
exercise already.

In this mode, I'm giving every Z3 call a time limit to make sure that the random
tests don't just take arbitrarily long. This means that asking Z3 to prove
something can have three outcomes, either it's proved, or Z3 finds a
counterexample, or Z3 times out.

Bugs Found
============

In addition to the two bugs I've already described, I'll briefly list the
additional bugs that were found by optimizing random traces and then trying to
prove the equivalence with Z3.

Most of the bugs were actually identified by optimizing random traces alone, not
by the Z3 component. They manifested as assert failures in the JIT compiler.

- The JIT concluded after ``12 == int_mul(x, 12)`` that ``x == 1``, which is
  incorrect if overflow occurred (a counterexample is ``0x8000000000000001``).

- An amusing bug, where from ``0 == int_lshift(0x1000000000000000, x)`` with
  ``x <= 0 <= 15``, the JIT concluded that ``0x1000000000000000 == 0``,
  triggering an assert. This wrong conclusion was again caused by not taking the
  possibility of overflow into account.

- A corner case in an optimization for chained integer additions with a
  constant, where in complex enough expressions, the wrong IR API was used
  (which works correctly in simple cases). Again, this triggered an assert.

This shows that we should have been fuzzing our JIT optimizer already (not a
surprising  observation in hindsight, fuzz all the things!).

Thankfully, there was also one further bug that really failed in the Z3
verifier. It's a bug in common subexpression elimination / arithmetic
simplification, which again does not take overflow correctly into account.

The buggy trace looks like this (unfortunately it's not easily possible to show
this bug in Python code).

.. code::

    [a, b]
    c = int_add(a, b)
    r = int_sub_ovf(c, b)
    guard_no_ovf()
    finish(r)

This was optimized to:

.. code::

    [a, b]
    finish(a)

Which is incorrect, because the guard can fail given the right inputs.
But the optimizer concluded that the subtraction is safe, because its the
inverse of an earlier addition, not taking into account that this earlier
addition can have overflowed.

Note that a related optimization is actually correct. Given this code:

.. code::

    [a, b]
    c = int_add_ovf(a, b)
    guard_no_ovf()
    r = int_sub(c, b)
    finish(r)

It can be optimized to:

.. code::

    [a, b]
    c = int_add_ovf(a, b)
    guard_no_ovf()
    finish(a)


Future Work and Conclusion
===========================

In the current form the Z3 checker is only a start, even though it has already
been concretely useful. There are various directions into which we could extend
it. In addition to generate random tests completely from scratch, we could also
start from the existing manually written unit-tests and randomly mutate those.

I also want to extend the Z3 checker with support more operations, heap
operations in particular (but it's not quite clear to me how to model garbage
collection).

I also want to try to switch the code away from the Z3 API and use the more
general smtlib__ interface directly, in order to be able to use other SMT
checkers than Z3, eg CVC4__.

.. __: https://smtlib.cs.uiowa.edu/
.. __: https://cvc4.github.io/

But all in all this was a fun and not too hard way to find a bunch of bugs in
our optimizer! And the infrastructure is now in place, which means that we run
some random test cases every time we execute our tests. This is going to be
particularly useful when we do further work on the integer reasoning of the JIT
(like Nico is doing, for example). As of time of writing of this post, all the
bugs mentioned have been fixed and the Z3 code has landed on the default branch
and runs as part of PyPy's CI infrastructure.

Acknowledgements
=================

Thanks to `Saam Barati`_, `Max Bernstein`_, `Joshua Schmidt`_ and `Martin
Berger`_, for great feedback on drafts of this post!

.. _`Saam Barati`: http://saambarati.org/
.. _`Max Bernstein`: https://bernsteinbear.com
.. _`Martin Berger`: https://martinfriedrichberger.net/
.. _`Joshua Schmidt`: https://www.cs.hhu.de/lehrstuehle-und-arbeitsgruppen/softwaretechnik-und-programmiersprachen/unser-team/team/schmidt
