.. title: A DSL for Peephole Transformation Rules of Integer Operations in the PyPy JIT
.. slug: jit-peephole-dsl
.. date: 2024-10-23 15:00:00 UTC
.. tags: jit, z3
.. category:
.. link:
.. description:
.. type: rest
.. author: CF Bolz-Tereick

As is probably apparent from the sequence of blog posts about the topic in the
last year, I have been thinking about and working on integer optimizations in the JIT
compiler a lot. This work was mainly motivated by Pydrofoil_, where integer
operations matter a lot more than for your typical Python program.

.. _Pydrofoil: https://docs.pydrofoil.org/en/latest/

In this post I'll describe my most recent change, which is a new small domain
specific language that I implemented to specify peephole optimizations on
integer operations in the JIT.
It uses pattern matching to specify how (sequences of) integer operations
should be simplified and optimized. The rules are then compiled to
RPython code that then becomes part of the JIT's optimization passes.

To make it less likely to introduce incorrect optimizations into the JIT, the
rules are automatically proven correct with Z3 as part of the build process (for
a more hands-on intro to how that works you can look at the `knownbits`__ post).
In this blog post I want to motivate why I introduced the DSL and give an
introduction to how it works.

.. __: https://pypy.org/posts/2024/08/toy-knownbits.html#proving-correctness-of-the-transfer-functions-with-z3

Motivation
===========================

This summer, after I wrote my `scripts to mine JIT traces for missed optimization`__
opportunities, I started implementing a few of the integer peephole rewrite that
the script identified. Unfortunately, doing so led to the problem that the way
we express these rewrites up to now is very imperative and verbose. Here's a
snippet of RPython code that shows some rewrites for integer multiplication
(look at the comments to see what the different parts actually do). You don't
need to understand the code in detail, but basically it's in very imperative
style and there's quite a lot of boilerplate.

.. __: /posts/2024/07/mining-jit-traces-missing-optimizations-z3.html

.. code:: python

    def optimize_INT_MUL(self, op):
        arg0 = get_box_replacement(op.getarg(0))
        b0 = self.getintbound(arg0)
        arg1 = get_box_replacement(op.getarg(1))
        b1 = self.getintbound(arg1)

        if b0.known_eq_const(1):
            # 1 * x == x
            self.make_equal_to(op, arg1)
        elif b1.known_eq_const(1):
            # x * 1 == x
            self.make_equal_to(op, arg0)
        elif b0.known_eq_const(0) or b1.known_eq_const(0):
            # 0 * x == x * 0 == 0
            self.make_constant_int(op, 0)
        else:
            for lhs, rhs in [(arg0, arg1), (arg1, arg0)]:
                lh_info = self.getintbound(lhs)
                if lh_info.is_constant():
                    x = lh_info.get_constant_int()
                    if x & (x - 1) == 0:
                        # x * (2 ** c) == x << c
                        new_rhs = ConstInt(highest_bit(lh_info.get_constant_int()))
                        op = self.replace_op_with(op, rop.INT_LSHIFT, args=[rhs, new_rhs])
                        self.optimizer.send_extra_operation(op)
                        return
                    elif x == -1:
                        # x * -1 == -x
                        op = self.replace_op_with(op, rop.INT_NEG, args=[rhs])
                        self.optimizer.send_extra_operation(op)
                        return
                else:
                    # x * (1 << y) == x << y
                    shiftop = self.optimizer.as_operation(get_box_replacement(lhs), rop.INT_LSHIFT)
                    if shiftop is None:
                        continue
                    if not shiftop.getarg(0).is_constant() or shiftop.getarg(0).getint() != 1:
                        continue
                    shiftvar = get_box_replacement(shiftop.getarg(1))
                    shiftbound = self.getintbound(shiftvar)
                    if shiftbound.known_nonnegative() and shiftbound.known_lt_const(LONG_BIT):
                        op = self.replace_op_with(
                                op, rop.INT_LSHIFT, args=[rhs, shiftvar])
                        self.optimizer.send_extra_operation(op)
                        return
            return self.emit(op)

Adding more rules to these functions is very tedious and gets super confusing
when the functions get bigger. In addition I am always worried about making
mistakes when writing this kind of code, and there is no feedback at all about
which of these rules are actually applied a lot in real programs.

Therefore I decided to write a small domain specific language with the goal of
expressing these rules in a more declarative way. In the rest of the post I'll
describe the DSL (most of that description is adapted from the documentation__
about it that I wrote).

.. __: https://rpython.readthedocs.io/en/latest/jit/ruleopt.html

The Peephole Rule DSL
============================

Simple transformation rules
--------------------------------------------------------------

The rules in the DSL specify how integer operation can be transformed into
cheaper other integer operations. A rule always consists of a name, a pattern,
and a target. Here's a simple rule::

    add_zero: int_add(x, 0)
        => x

The name of the rule is ``add_zero``. It matches operations in the trace of the
form ``int_add(x, 0)``, where ``x`` will match anything and ``0`` will match only the
constant zero. After the ``=>`` arrow is the target of the rewrite, i.e. what the
operation is rewritten to, in this case ``x``.

The rule language has a list of which of the operations are commutative, so ``add_zero``
will also optimize ``int_add(0, x)`` to ``x``.

Variables in the pattern can repeat::

    sub_x_x: int_sub(x, x)
        => 0

This rule matches against ``int_sub`` operations where the two arguments are the
same (either the same box, or the same constant).

Here's a rule with a more complicated pattern::

    sub_add: int_sub(int_add(x, y), y)
        => x

This pattern matches ``int_sub`` operations, where the first argument was
produced by an ``int_add`` operation. In addition, one of the arguments of the
addition has to be the same as the second argument of the subtraction.

The constants ``MININT``, ``MAXINT`` and ``LONG_BIT`` (which is either 32 or 64,
depending on which platform the JIT is built for) can be used in rules, they
behave like writing numbers but allow bit-width-independent formulations::

    is_true_and_minint: int_is_true(int_and(x, MININT))
        => int_lt(x, 0)

It is also possible to have a pattern where some arguments needs to be a
constant, without specifying which constant. Those patterns look like this::

    sub_add_consts: int_sub(int_add(x, C1), C2) # incomplete
        # more goes here
        => int_sub(x, C)

Variables in the pattern that start with a ``C`` match against constants only.
However, in this current form the rule is incomplete, because the variable ``C``
that is being used in the target operation is not defined anywhere. We will see
how to compute it in the next section.

Computing constants and other intermediate results
--------------------------------------------------------------

Sometimes it is necessary to compute intermediate results that are used in the
target operation. To do that, there can be extra assignments between the rule head
and the rule target.::

    sub_add_consts: int_sub(int_add(x, C1), C2) # incomplete
        C = C1 + C1
        => int_sub(x, C)

The right hand side of such an assignment is a subset of Python syntax,
supporting arithmetic using ``+``, ``-``, ``*``, and certain helper functions.
However, the syntax allows you to be explicit about unsignedness for some
operations. E.g. ``>>u`` exists for unsigned right shifts (and I plan to add
``>u``, ``>=u``, ``<u``, ``<=u`` for comparisons).

Here's an example of a rule that uses ``>>u``::

    urshift_lshift_x_c_c: uint_rshift(int_lshift(x, C), C)
        mask = (-1 << C) >>u C
        => int_and(x, mask)


Checks
--------------------------------------------------------------

Some rewrites are only true under certain conditions. For example,
``int_eq(x, 1)`` can be rewritten to ``x``, if ``x`` is known to store a boolean value. This can
be expressed with *checks*::

    eq_one: int_eq(x, 1)
        check x.is_bool()
        => x

A check is followed by a boolean expression. The variables from the pattern can
be used as ``IntBound`` instances in checks (and also in assignments) to find out
what the abstract interpretation of the JIT knows about the value of a trace variable
(``IntBound`` is the name of the abstract domain that the JIT uses for integers,
despite the fact that it also stores knownbits__ information nowadays).

.. __: /posts/2024/08/toy-knownbits.html

Here's another example::

    mul_lshift: int_mul(x, int_lshift(1, y))
        check y.known_ge_const(0) and y.known_le_const(LONG_BIT)
        => int_lshift(x, y)

It expresses that ``x * (1 << y)`` can be rewritten to ``x << y`` but checks that
``y`` is known to be between ``0`` and ``LONG_BIT``.

Checks and assignments can be repeated and combined with each other::

    mul_pow2_const: int_mul(x, C)
        check C > 0 and C & (C - 1) == 0
        shift = highest_bit(C)
        => int_lshift(x, shift)

In addition to calling methods on ``IntBound`` instances, it's also possible to
access their attributes, like in this rule::

    and_x_c_in_range: int_and(x, C)
        check x.lower >= 0 and x.upper <= C & ~(C + 1)
        => x



Rule Ordering and Liveness
--------------------------------------------------------------

The generated optimizer code will give preference to applying rules that
produce a constant or a variable as a rewrite result. Only if none of those
match do rules that produce new result operations get applied. For example, the
rules ``sub_x_x`` and ``sub_add`` are tried before trying ``sub_add_consts``,
because the former two rules optimize to a constant and a variable
respectively, while the latter produces a new operation as the result.

The rule ``sub_add_consts`` has a possible problem, which is that if the
intermediate result of the ``int_add`` operation in the rule head is used by
some other operations, then the ``sub_add_consts`` rule does not actually
reduce the number of operations (and might actually make things slightly worse
due to increased register pressure). However, currently it would be extremely
hard to take that kind of information into account in the optimization pass of
the JIT, so we optimistically apply the rules anyway.

Checking rule coverage
--------------------------------------------------------------

Every rewrite rule should have at least one unit test where it triggers. To
ensure this, the `unit test file that mainly checks integer optimizations`__ in the
JIT has an assert at the end of a test run, that every rule fired at least once.

.. __: https://github.com/pypy/pypy/blob/d92d0bfd38318ede1cbaadadafd77da69d431fad/rpython/jit/metainterp/optimizeopt/test/test_optimizeintbound.py

Printing rule statistics
--------------------------------------------------------------

The JIT can print statistics about which rule fired how often in the
``jit-intbounds-stats`` logging category, using the `PYPYLOG`_ mechanism. For
example, to print the category to stdout at the end of program execution, run
PyPy like this::

    PYPYLOG=jit-intbounds-stats:- pypy ...

The output of that will look something like this::

    int_add
        add_reassoc_consts 2514
        add_zero 107008
    int_sub
        sub_zero 31519
        sub_from_zero 523
        sub_x_x 3153
        sub_add_consts 159
        sub_add 55
        sub_sub_x_c_c 1752
        sub_sub_c_x_c 0
        sub_xor_x_y_y 0
        sub_or_x_y_y 0
    int_mul
        mul_zero 0
        mul_one 110
        mul_minus_one 0
        mul_pow2_const 1456
        mul_lshift 0
    ...

.. _`PYPYLOG`: https://rpython.readthedocs.io/en/latest/logging.html

Termination and Confluence
--------------------------------------------------------------

Right now there are unfortunately no checks that the rules actually rewrite
operations towards "simpler" forms. There is no cost model, and also nothing
that prevents you from writing a rule like this::


    neg_complication: int_neg(x) # leads to infinite rewrites
        => int_mul(-1, x)

Doing this would lead to endless rewrites if there is also another rule that
turns multiplication with -1 into negation.

There is also no checking for confluence__ (yet?), i.e. the property that all
rewrites starting from the same input trace always lead to the same output
trace, no matter in which order the rules are applied.

.. __: https://en.wikipedia.org/wiki/Confluence_(abstract_rewriting)


Proofs
--------------------------------------------------------------

It is very easy to write a peephole rule that is not correct in all corner
cases. Therefore all the rules are proven correct with Z3 before compiled into
actual JIT code, by default. When the proof fails, a (hopefully minimal)
counterexample is printed. The counterexample consists of values for all the
inputs that fulfil the checks, values for the intermediate expressions, and
then two *different* values for the source and the target operations.

E.g. if we try to add the incorrect rule::

    mul_is_add: int_mul(a, b)
        => int_add(a, b)

We get the following counterexample as output::

    Could not prove correctness of rule 'mul_is_add'
    in line 1
    counterexample given by Z3:
    counterexample values:
    a: 0
    b: 1
    operation int_mul(a, b) with Z3 formula a*b
    has counterexample result vale: 0
    BUT
    target expression: int_add(a, b) with Z3 formula a + b
    has counterexample value: 1

If we add conditions, they are taken into account and the counterexample will
fulfil the conditions::

    mul_is_add: int_mul(a, b)
        check a.known_gt_const(1) and b.known_gt_const(2)
        => int_add(a, b)

This leads to the following counterexample::

    Could not prove correctness of rule 'mul_is_add'
    in line 46
    counterexample given by Z3:
    counterexample values:
    a: 2
    b: 3
    operation int_mul(a, b) with Z3 formula a*b
    has counterexample result vale: 6
    BUT
    target expression: int_add(a, b) with Z3 formula a + b
    has counterexample value: 5

Some ``IntBound`` methods cannot be used in Z3 proofs because their `control
flow is too complex`__. If that is the case, they can have Z3-equivalent
formulations defined (in every case this is done, it's a potential proof hole if
the Z3 friendly reformulation and the real implementation differ from each
other, therefore extra care is required to make very sure they are equivalent).

.. __: /posts/2024/08/toy-knownbits.html#cases-where-this-style-of-z3-proof-doesnt-work).

It's possible to skip the proof of individual rules entirely by adding
``SORRY_Z3`` to its body (but we should try not to do that too often)::

    eq_different_knownbits: int_eq(x, y)
        SORRY_Z3
        check x.known_ne(y)
        => 0

Checking for satisfiability
--------------------------------------------------------------

In addition to checking whether the rule yields a correct optimization, we also
check whether the rule can ever apply. This ensures that there are *some*
runtime values that would fulfil all the checks in a rule. Here's an example of
a rule violating this::

    never_applies: int_is_true(x)
        check x.known_lt_const(0) and x.known_gt_const(0) # impossible condition, always False
        => x

Right now the error messages if this goes wrong are not completely easy to
understand. I hope to be able to improve this later::

    Rule 'never_applies' cannot ever apply
    in line 1
    Z3 did not manage to find values for variables x such that the following condition becomes True:
    And(x <= x_upper,
        x_lower <= x,
        If(x_upper < 0, x_lower > 0, x_upper < 0))


Implementation Notes
--------------------------------------------------------------

The implementation of the DSL is done in a relatively ad-hoc manner. It is
parsed using `rply`__, there's a small type checker that tries to find common
problems in how the rules are written. Z3 is used via the Python API, like in
the previous blog posts that are using it. The
pattern matching RPython code is generated using an approach inspired by Luc
Maranget's paper `Compiling Pattern Matching to Good Decision Trees`__. See
`this blog post`__ for an approachable introduction.

.. __: https://rply.readthedocs.io/
.. __: http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf
.. __: https://compiler.club/compiling-pattern-matching/

Conclusion
=====================================================

Now that I've described the DSL, here are the rules that are equivalent to the
imperative code in the motivation section::

    mul_zero: int_mul(x, 0)
        => 0

    mul_one: int_mul(x, 1)
        => x

    mul_minus_one: int_mul(x, -1)
        => int_neg(x)

    mul_pow2_const: int_mul(x, C)
        check C > 0 and C & (C - 1) == 0
        shift = highest_bit(C)
        => int_lshift(x, shift)

    mul_lshift: int_mul(x, int_lshift(1, y))
        check y.known_ge_const(0) and y.known_le_const(LONG_BIT)
        => int_lshift(x, y)


The current status of the DSL is that it got merged to PyPy's main branch. I
rewrote a part of the integer rewrites `into the DSL`__, but some are still in the
old imperative style (mostly for complicated reasons, the easily ported ones are
all done). Since I've only been porting optimizations that had existed prior to
the existence of the DSL, performance numbers of benchmarks didn't change.

.. __: https://github.com/pypy/pypy/blob/d92d0bfd38318ede1cbaadadafd77da69d431fad/rpython/jit/metainterp/ruleopt/real.rules

There are a number of features that are still missing and some possible
extensions that I plan to work on in the future:

- All the integer operations that the DSL handles so far are the variants that
  do not check for overflow (or where overflow was proven to be impossible to
  happen). In regular Python code the overflow-checking variants `int_add_ovf`
  etc are much more common, but the DSL doesn't support them yet. I plan to fix
  this, but don't completely understand how the correctness proofs for them
  should be done correctly.

- A related problem is that I don't understand what it means for a rewrite to be
  correct if some of the operations are only defined for a subset of the input
  values. E.g. division isn't defined if the divisor is zero. In theory, a
  division operation in the trace should always be preceded by a check that the
  divisor isn't zero. But sometimes other optimization move the check around and
  the connection to the division gets lost or muddled. What optimizations can we
  still safely perform on the division? There's lots of prior work on this
  question, but I still don't understand what the correct approach in our
  context would be.

- Ordering comparisons like ``int_lt``, ``int_le`` and their unsigned variants are
  not ported to the DSL yet. Comparisons are an area where the JIT is not super
  good yet at optimizing away operations. This is a pretty big topic and I've
  started a project with Nico Rittinghaus to try to improve the situation a bit
  more generally.

- A more advanced direction of work would be to implement a simplified form of
  `e-graphs`__ (or `ae-graphs`__). The JIT has like half of an e-graph data
  structure already, and we probably can't afford a full one in terms of compile
  time costs, but maybe we can have two thirds or something?


.. __: https://egraphs-good.github.io/
.. __: https://vimeo.com/843540328

Acknowledgements
========================

Thank you to `Max Bernstein`__ and `Martin Berger`__ for super helpful feedback on
drafts of the post!

.. __: https://bernsteinbear.com/

.. __: https://martinfriedrichberger.net/
