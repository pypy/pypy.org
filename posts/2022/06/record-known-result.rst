.. title: A Hint for Language-Specific Runtime Function Optimization in RPython's Meta-JIT
.. slug: record-known-result
.. date: 2022-06-01 15:00:00 UTC
.. tags: jit
.. category: 
.. link: 
.. description: 
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

==================================================================================
A Hint for Language-Specific Runtime Function Optimization in RPython's Meta-JIT
==================================================================================

RPython's meta-JIT cannot reason about the properties of many RPython
implementation-level functions, because those are often specific to the
different interpreters written in RPython. Expressing language-specific
optimizations on these functions would allow the JIT to more effectively reason
about language-specific data structures and potentially remove costly calls
into the runtime support code. In this blog post I will describe a new hint
that makes it possible to express invariants about the functions of the data
structures used in a specific language interpreter. These hints make it
possible for the meta-JIT optimizer to do more language-specific optimizations
without having to change the meta-JIT itself.

Introduction and Background
===========================

RPython has a meta-JIT, that can be applied to a variety of languages, one of
them being PyPy, a Python implementation (that's really two implementations,
one PyPy2, one PyPy3). Most modern languages have many
built-in functions and data-types that are written in the implementation
language (RPython, in our case, C in the case of CPython). We want the JIT
optimizer to be able to reason about these functions and datatypes.

One way to do this would be to extend the meta-JIT by adding a new language-specific
optimization pass that knows how to deal with these functions. This approach
however goes against the idea of a meta-JIT, since we want the JIT to be
language independent. So we developed various tools in the past that make it
possible for the author of RPython interpreters to express various
optimizations. One of the very important ones that has been there forever is
the ``@elidable`` decorator, which makes it possible to mark an RPython
function as pure (actually a small generalization, but for the purpose of this
post thinking of them as pure is fine). This decorator was described `in a blog
post in 2011`__, it was still called ``@purefunction`` then. The post later
turned into a paper__.

.. __: https://www.pypy.org/posts/2011/03/controlling-tracing-of-interpreter-with-871085470935630424.html
.. __: https://www3.hhu.de/stups/downloads/pdf/BoCuFiLePeRi11.pdf

An elidable function will be constant-folded by the JIT if all its arguments
are constant. If it can't be removed because some arguments aren't constant,
it's still subject to `common subexpression elimination`__ (CSE). Subsequent
calls to the same function with the same arguments can be removed and replaced
by the previous result.

.. __: https://en.wikipedia.org/wiki/Common_subexpression_elimination

There are lots of examples of ``@elidable`` functions, both in RPython in
general and in the PyPy interpreter. In the post linked above they are used for
optimizing object operations in a tiny interpreter.

But also a lot of functionality that is more directly exposed to the Python
programmer is elidable. Most string methods are elidable for example:
``str.lower`` will always return the same result for some argument, and if you
call it twice on the same string, it will also return the same result. So
adding the ``@elidable`` decorator to the implementation of the string method
allows the JIT to constant-fold it if it's applied to a constant string, and to
remove a second identical call. Another big class of examples are all the
implementation functions for our big integer operations, which underlie the
Python ``int`` type once the values don't fit into a machine word anymore. On
the implementation level we implement those in an ``rbigint`` class, and most
methods of that are also elidable. This enables the JIT to constant-fold big
integer addition, and do CSE on big integer arithmetic.

This is all very useful! But it's still only a limited amount of things that
the interpreter author can express to the JIT with this one function decorator.
Recently I merged a branch that adds two new hints at the interpreter author
can use to communicate possible optimizations to the meta-JIT! The work has
been happening on and off in the last three years, the scope was a bit too big
and some parts were not done and I didn't seem to converge either. So I
recently decided that this was going on for too long already and to merge a
minimal version of the branch, which contains only the support for the two new
hints, but not really many interesting *applications* for the hints to the PyPy
interpreter. Those can be added in a much more localized fashion over time.

``record_known_result``
=======================

So, what are the hints? One of them is called ``record_known_result``, and that
hint is what this blog post is about. The one one of them is called
``record_exact_value``, it's conceptually quite simple, but it's much harder to
see how it can be used. It was implemented by Lin Cheng from Cornell, and it is
described (together with a possible optimization) in another paper__ – I will
talk about that one in a later post, if I get to it.

What is ``record_exact_value`` used for? One of the limitations of ``elidable``
is that often there are properties that connect *several* function calls that
are connected in some way. Sometimes there are functions that are inverses of
each other, so that ``f(g(x)) == x``  for all ``x`` (example: negation on
numbers is its own inverse, ``--x == x``). Sometimes functions are
*idempotent__*, which means that if you call the function several times you can
remove all but the first call. An example would be ``abs`` on numbers, after
the first call to ``abs`` the result is positive, so calling the function again
on the result has no effect, i.e. ``abs(abs(x)) == abs(x)``. These properties
could in theory be nicely used by a hypothetical optimizer that knows about
them and the functions. However, as described above, we don't want to change
the meta-JIT to add knowledge about interpreter-specific functionality. So we
wanted to add a hint that can express them to the meta-JIT.

.. __: https://en.wikipedia.org/wiki/Idempotence#Idempotent_functions

What could hints look like, that make it possible to express these
properties? At first I was experimenting with some declarative decorators
like ``@idempotent`` and ``@is_inverse_of(func)`` but I felt like it wouldn't
scale to add lots of these decorators and support for all of them in the
meta-JIT. In the end I found a not fully obvious hint that is not a
decorator, that is powerful enough to implement at least these last two and a
whole bunch of other patterns. This hint piggy-backs on the existing CSE
implementation of pure functions in the meta-JIT.

The hint works as follows: It is a new function called
``record_known_result(result, func, *args)``. Calling that function has no
direct effect at runtime. Instead, it communicates to the meta-JIT, that if
it sees a function call to ``func`` with the arguments ``*args``, it can replace
the result of that function call with ``res``.

Since this is pretty abstract, it's best to look at an example. How would you
use this to express the fact that ``rbigint_neg`` is its own inverse, which is
function in the runtime that is responsible for computing the negative value
of a big integers? The implementation of ``rbigint_neg`` looks roughly like
this (it's actually a method and a tiny bit more complicated, but not really
significantly so):

.. code:: python

    @elidable
    def rbigint_neg(self):
        return rbigint(digits=self.digits, sign=-self.sign)

If we want to use the new hint to express that ``rbigint_neg(rbigint_neg(x)) ==
x``, we need to rewrite the function somewhat, by introducing a pure helper
function that does the actual computation, and turning the original function
into a wrapper that calls the helper:

.. code:: python

    @elidable
    def _rbigint_neg_helper(self):
        return rbigint(digits=self.digits, sign=-self.sign)
        
    def rbigint_neg(self):
        res = _rbigint_neg_helper(self)
        record_known_result(self, _rbigint_neg_helper, res)
        return res

``record_known_result`` is a new function in the ``rpython.rlib.jit`` library that
has the signature ``record_known_result(result, function, *args)``. What does
this function do? Outside of the JIT, a call to that function is simply
ignored. But when we trace the ``rbigint_neg`` function the hint tells the JIT
the following information: if at any point in the future (meaning further down the
trace) we see another call to ``_rbigint_neg_helper`` with ``res`` as the argument,
we can replace that call directly with ``self``, which is exactly the property
that ``_rbigint_neg_helper`` is its own inverse. As another example, let's
express the idempotence of ``bytes.lower``. We can imagine the implementation
looking something like this (`the "real" implementation`__ is actually quite
different in practice, we don't want the extra copy of ``bytes.join``):

.. __: https://foss.heptapod.net/pypy/pypy/-/blob/ab597702f7d9a267d3ae7c3fc91a5f25cd36a12e/rpython/rtyper/lltypesystem/rstr.py#L526

.. code:: python

    @elidable
    def bytes_lower(b):
        # implementation looks very different in practice, just an illustration!
        res = ['\x00'] * len(b)
        for i, c in enumerate(b):
            if 'A' <= c <= 'Z':
                c = chr(ord(c) - ord('A') + ord('a'))
            res[i] = c
        return b"".join(res)

To express that the function is idempotent, we need to express that
``bytes_lower(bytes_lower(b)) == b``. We express this again with the same
approach, move the implementation into a helper function, call the helper from
the original function and call ``record_known_result`` too:

.. code:: python

    @elidable
    def _bytes_lower_helper(b):
        ... # as above

    def bytes_lower(b):
        res = _bytes_lower_helper(b)
        record_known_result(res, _bytes_lower_helper, res)
        return res


This tells the meta-JIT that if ``res`` is later itself passed to
``_bytes_lower_helper``, it can remove that call and replace it immediately
with ``res`` (because ``res`` is already all lower cased, as its the result of
a call to ``lower``), i.e. that ``_bytes_lower_helper`` is idempotent. (There
are also other properties of lower and upper we could express in this way, for
example that ``bytes.lower(bytes.upper(x)) == bytes.lower(x)``, let's leave it
at that for now though).

Both of these usage patterns of ``record_known_result`` could of course also be
pulled out into general decorators again. For example a generic ``@idempotent``
decorator could be implemented like this:

.. code:: python

    def idempotent(func):
        func = elidable(func) # idempotent implies elidable
        def wrapper(arg):
            res = func(arg)
            record_known_result(res, func, res)
            return res
        return wrapper

Then the decorator could be used like this for ``bytes_lower``:

.. code:: python

    @idempotent
    def bytes_lower(b):
        # implementation as in the original code above
        ...


Implementing ``record_known_result``
========================================

How is ``record_known_result`` implemented? As I wrote above, the implementation
of that hint is piggy-backing on the existing support for ``elidable`` functions
in the optimizer of the meta-JIT. There are several optimizations that do
something with elidable function calls: `constant folding`__, CSE__, `dead code
elimination`__. Let's look at those work on ``elidable`` functions:

 - Constant folding removes calls to elidable functions with constant results
   (technically this is a bit complicated, but conceptually this is what
   happens).
 - CSE will replace calls to an elidable function by previous results, if they
   appear a second time further down the trace.
 - Dead code elimination will remove elidable function calls in the trace that
   have unused results.

.. __: https://en.wikipedia.org/wiki/Constant_folding
.. __: https://en.wikipedia.org/wiki/Common_subexpression_elimination
.. __: https://en.wikipedia.org/wiki/Dead_code_elimination

So if there is a trace like this:

.. code:: 

    r1 = call_elidable((f), (1)) # constant-folded to, say, 17
    r2 = call_elidable((g), a, b)
    r3 = call_elidable((g), a, b) # replaced by r2
    r4 = call_elidable((h), c, d) # removed, result unused
    print(r1, r2, r3)

It will be optimized to:

.. code::

    r2 = call_elidable((g), a, b)
    print((17), r2, r2)

Some general notes about these traces: They are all in `single-static-assignment
form`__ (SSA), meaning that every variable is assigned to only once. In fact,
there is not really a concept of "variable" at all, instead all variables are
identical with the operations that produce them.

.. __: https://en.wikipedia.org/wiki/Static_single_assignment_form

Let's look at how the CSE pass that optimizes elidable calls, that is part of
the meta-JIT works. In pseudocode it could look something like this:

.. code:: python

    def cse_elidable_calls(trace):
        seen_calls = {}
        output_trace = []
        for op in trace:
            if is_call_elidable(op):
                key = op.args # the function, followed by the argument variables/consts
                previous_op = seen_calls.get(key)
                if previous_op is not None:
                    replace_result_with(op, previous_op)
                    # don't need to emit the op
                    continue
                else:
                    seen_calls[key] = op
            output_trace.append(op)
        return output_trace

There is quite a bit of hand-waving here, particularly around how
``replace_result_with`` can work. But this is conceptually what the real
optimization does (Some details on the hand-waving: replacing ops with other ops
is implemented using a union-find__ data-structure to efficiently allow doing
arbitrary replacements. These replacements need to influence the lookup in the
``seen_calls`` dict, so in practice it's not even a dictionary at all. Another
way that the pseudocode is simplified is that we don't in practice have tiny
passes like this that go over the trace again and again. Instead, we have a
single optimization pass that goes over the trace in forward direction once).

.. __: https://en.wikipedia.org/wiki/Disjoint-set_data_structure

Making use of the information provided by ``record_known_result`` is done by
changing the CSE pass in particular. Let's say you trace something like this:

.. code:: python

    x = bytes_lower(s)
    ... some other code ...
    y = bytes_lower(x)
    print(x, y)


This should  trigger the idempotence optimization. The resulting trace could
look like this:

.. code::

    # bytes_lower itself is inlined into the trace:
    r1 = call_elidable((_bytes_lower_helper), s1)
    record_known_result(r1, (_bytes_lower_helper), r1)
    ... intermediate operations ...
    # second call to bytes_lower inlined into the trace:
    r2 = call_elidable((_bytes_lower_helper), r1) # replace r2 with r1
    record_known_result(r2, (_bytes_lower_helper), r2)
    print(r1, r2)

The CSE pass on elidable functions will now optimize away the call that results
in ``r2``. It does this not by replacing ``r2`` by a previous call to
``_bytes_lower_helper`` with the same arguments (such a call doesn't exist),
but instead makes use of the information conveyed by the first
``record_known_result`` trace operation. That operation states that if you see
a call like the second ``_bytes_lower_helper`` you can replace it with ``r1``.
The resulting optimized trace therefore looks like this:

.. code:: 

    r1 = call_elidable((_bytes_lower_helper), s1)
    ... intermediate optimizations, optimized ...
    # call removed, r2 replaced with r1 in the rest of the trace
    print(r1, r1)

The ``record_known_result`` operations are also removed, because further
optimization passes and the backends don't need them. To get this effect, we
have to change the pseudocode above to teach the CSE pass about
``record_known_result`` operations in the following way:

.. code:: python

    def cse_elidable_calls(trace):
        seen_calls = {}
        output_trace = []
        for op in trace:
            # <---- start new code
            if is_record_known_result(op):
                key = op.args[1:] # remove the first argument, which is the result
                seen_calls[key] = op.args[0]
                continue # don't emit the record_known_result op
            # <---- end new code
            if is_call_elidable(op):
                key = (op.call_target, op.args)
                previous_op = seen_calls.get(key)
                if previous_op is not None:
                    replace_result_with(op, previous_op)
                    # don't need to emit the op
                    continue
                else:
                    seen_calls[key] = op
            output_trace.append(op)
            return output_trace

That's all! So from the point of view of the implementation of CSE of elidable
functions, the new hint is actually very natural.

In the case of function inverses, dead code elimination also plays an important
role. Let's look at the trace of a double negation, maybe like this: ``x = -y;
...; print(-x)``:

.. code:: 

    r1 = call_elidable((_rbigint_neg_helper), a1)
    record_known_result(a1, (_rbigint_neg_helper), r1)
    ... intermediate stuff
    r2 = call_elidable((_rbigint_neg_helper), r1) # replace r2 with a1
    record_known_result(r1, (_rbigint_neg_helper), r2)
    print(r2)

After CSE, the second call is removed and the trace looks like this, because
``r2`` was found to be the same as ``a1``:

.. code:: 

    r1 = call_elidable((_rbigint_neg_helper), a1) # dead
    ... intermediate stuff, CSEd
    # call removed
    print(a1)

Now dead code elimination notices that the first call is not needed any more
either and removes it.

What is good about this design? It very neatly ties into the existing
infrastructure and is basically only about 100 lines of changes in the
meta-JIT. The amount of work the optimizer does stays essentially the same, as
the new hints are basically directly usable by CSE which we already do anyway.

Performance effects
====================

So far, we haven't actually used this new hint in PyPy much! At this point, the
hint is only a new tool in the interpreter author toolbox, and we still need to
find the best places to use this tool. The only use of the hint so far is an
annotation that tells the JIT that encoding and decoding to and from utf8 are
inverses of each other, to be able to optimize this kind of code:
``x = someunicode.encode("utf-8").decode("utf-8")`` by replacing ``x`` with
``someunicode`` (of course in practice there is usually again some distance
between the encode and decode calls). This happens in a bunch of places in real
code that I saw, but I didn't do a super careful study of what the performance
effect is yet.

Limitations
=============

What are the problems and the limitations of the approach I described in this
post?

Correctness remains tricky! If you write the wrong hints, the meta-JIT will
potentially miscompile your users' programs. To at least get some signal for
that, ``record_known_result`` actually performs the hinted call and does an
assert on the result if you run the program untranslated while executing tests.
In combination with for example property-based testing this can find a lot of
the bugs, but is of course no guarantee.

Many things aren't expressible! A lot less powerful than some of the recent
pattern based optimization systems that allow the non-compiler authors to
express rewrites. Instead, we designed the hint to minimally fit into the
existing optimizers at the cost of power and (partly) ease of use. The most
obvious limitation compared to pattern based approaches is that the
``record_known_result`` hint cannot quantify over unknown values, only use once
that are available in the program. As an example, it's not really possible to
express that ``bigint_sub(x, x) == bigint(0)`` *for arbitrary big integers
``x``*.

Another limitation of the hint is that currently it is only applicable to
pure/elidable functions. This makes it not really applicable to any kind of
*mutable* data structure. As an example, in theory ``sorted(list)`` is
idempotent, but only as long as the lists involved aren't mutated between the
two calls to ``sorted``. Reasoning about mutation doesn't really fit into the
model easily. The meta-JIT itself is actually able to do a lot of tracking of
what kinds of mutations occurred and what the heap must look like. But we
haven't found a good way to combine this available information with
user-provided information about function behaviour.

Conclusion
==============

A new hint! Such power, much brainbendyness!
