<!--
.. title: Finding Missing JIT Compiler Optimizations with Z3
.. slug: finding-missing-optimizations-z3
.. date: 2024-07-07 19:14:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: CF Bolz-Tereick
-->

Last week I was at the [PLDI conference](https://pldi24.sigplan.org/) in
Copenhagen to present a [paper](https://dl.acm.org/doi/10.1145/3652588.3663316)
I co-authored with [Max Bernstein](https://bernsteinbear.com/). I also finally
met [John Regehr](https://blog.regehr.org/), who I'd been talking on social
media for a long time but had never met. John has been working on compiler
correctness and better techniques for building compilers and optimizers since a
very long time. The blog post [Finding JIT Optimizer Bugs using SMT Solvers and
Fuzzing](https://www.pypy.org/posts/2022/12/jit-bug-finding-smt-fuzzing.html)
was heavily inspired by this work. We talked a lot about his and his groups
work on using Z3 to find missing optimizations.

In my previous blog post about finding optimizer bugs, I described how to use
Z3 (an SMT solver) and fuzzing to find bugs in the integer optimization passes
of PyPy's JIT. In this post I want to talk about early results from an
experiment that came out of discussions with John (and also inspired by a talk
by Nikolai Tillmann about
[SPUR](https://web.archive.org/web/20130503204413/http://www.cs.iastate.edu/~design/vmil/2010/slides/p03-tillmann-slides.pdf)
that I saw many years ago). In this experiment I try to use Z3 to find missing
[peephole optimizations]() for integer operations in the traces of PyPy's JIT.

## Motivation 

PyPy's JIT has historically always focused almost exclusively on the typical
inefficiencies of Python programs, such as removing boxing, run-time type
feedback, speculation type-specializing collections, etc. However, in the last
two years I have applied the JIT also to a very different domain, that of CPU
emulation, in the experimental [Pydrofoil](https://docs.pydrofoil.org) project
(supports RISC-V and ARM by now). For Pydrofoil, the performance of integer
operations is significantly more important than for "normal" Python code, which
is why I've become much more interested in optimizing integer operations.

Finding missing optimizations is quite hard to do manually, because it involves
carefully staring at huge concrete traces of programs that we care about. So
ideally we want to automate the problem. To make sure that we care about the
optimizations that we find, we start from the traces of benchmarks that are
interesting, such as booting Linux on the ARM and RISC-V emulators.

We could find missing optimizations by using LLVM or GCC if we could translate
RPython JIT traces to C code. But then we would be relying on the quality of
GCC optimizations. Instead, we will use Z3, an SMT ('satisfiability modulo
theories') solver by Microsoft Research, which was an excellent Python API. Z3
has excellent support for reasoning about bitvectors, and we will use that to
identify non-optimal integer operation sequences.

## Background Z3

Z3 is a STM solver, which means that it can answer the question whether a
certain formula is satisfiable. This means that it will try to find concrete
values for all the variables that occur in the formulas such that the formula
becomes true. The formulas can be about objects in various theories, Z3 has
support for (mathematical) integers, strings, arrays, unterinterpreted
functions, etc. The theory we care about in this blog post is the **bitvector**
theory. Bitvectors are vectors of bits of a fixed size, and they are great for
expressing operations on machine integers with a fixed bit width. We use Z3
extensively to fuzz the JIT's optimizer, so we already have a translation from
JIT integer operations to Z3 formulas. I'm just reusing some of that
infrastructure for finding missing optimizations.

To give a bit of an idea of what using the Z3 Python API looks like, here's an
example. Suppose we want to check that `x ^ -1` is the same as `~x` for
arbitrary 64-bit integers (this is true because xor with a 1 bit flips the bit
in `x`, and `-1` has all bits set in two's complement). 

```pycon
>>>> import z3
>>>> a = z3.BitVec('a', 64) # we construct a bitvector variable with width 64
>>>> a ^ -1 == ~a # the variables have operators overloaded, so we can combine them into larger formulas
a ^ 18446744073709551615 == ~a
>>>> z3.prove(a ^ -1 == ~a) # now we can ask Z3 to prove the formula
proved
>>>> z3.prove(a ^ -1 == a) # try to prove something wrong
counterexample
[a = 0]
```

Or, an example with two variables: `a * (1 << b)` is the same as `a << b`:

```pycon
>>>> b = z3.BitVec('b', 64)
>>>> solver.prove(a * (1 << b) == a << b)
proved
```

## General Recipe for Finding Missing Optimizations 

Now that we have an idea how Z3 and bitvectors work, we want to use it to find
missing integer optimizations in the PyPy JIT. The general approach is to first
collect a bunch of traces of integer heavy programs. Then we encode the integer
operations in the traces into Z3 formulas and use different Z3 queries to
identify inefficiencies in the traces. Once we found an inefficiency, we try to
minimize the trace to the smallest trace that we can get that still shows an
inefficiency to make it easier to understand. Then we inspect the minimized
cases manually and (if possible) try to implement the missing optimizations.
I'll write about each of these steps in turn.

## Encoding Traces as Z3 formulas 

The blog post about [using Z3 to find bugs]() already contained the code to
encode PyPy trace operations into Z3 formulas, so we don't need to repeat that
here. But to give an example, XXX

## Identifying constant booleans with Z3

The very simplest thing we can try to find inefficient parts of the traces is
to first focus on boolean variables. They are represented as word-sized ints
with values 0 and 1 in PyPy's JIT. For every boolean variable in the trace we
can ask Z3 to prove that this variable must be always True or always False.
Most of the time, neither of these proofs will succeed. But if Z3 manages to
prove one of them, we know have found an ineffiency: instead of computing the
boolean result (eg by executing a comparison) we could have replaced the
operation with the corresponding constant.

Here's an example of an inefficiency found that way: if `x < y` and `y < z` are
both true, PyPy's JIT isn't able to conclude from that that `x < z` must also
be true. The JIT reasons about the concrete ranges (lower and upper bounds) for
every integer variable, but it has no way to remember anything about
relationships between different variables. This kind of reasoning would quite
often be useful to remove list/string bounds checks. Here's a [talk about how
LLVM does this](https://www.youtube.com/watch?app=desktop&v=1hm5ZVmBEvo) (but
it might be too heavyweight for a JIT setting).

Here are some more examples found that way:

- `x - 1 == x` is always False 
- `x - (x == -1) == -1` is always False. The pattern `x - (x == -1)` happens a
  lot in PyPy's hash computations: To be compatible with the CPython hashes we
  need to make sure that no object's hash is -1 (CPython uses -1 as an error
  value on the C level).

## Identifying redundant operations 

A more interesting class of redundancy is to try to find two operations in a
trace that compute the same result. We can do that by asking Z3 to prove for
each pair of different operations in the trace to prove that the result is
always the same. If a previous operation returns the same result, the JIT could
have re-used that result instead of re-computing it, saving time. Doing this
search for equivalent operations with Z3 is quadratic in the number of
operations, but since traces have a maximum length it is not too bad in
practice.

This is the real workhorse of my script so far, it's what finds most of the
inefficiencies. Here's a few examples:

- The very first and super useful example the script found is `int_eq(b, 1) ==
  b` if `b` is known to be a boolean (ie and integer 0 or 1). I have already
  implemented this optimization in the JIT.
- Similarly, `int_and(b, 1) == b` for booleans.
- `(x << 4) & -0xf == x << 4`
- `((x >> 63) << 1) << 2) >> 3 == x >> 63`. In general the JIT is quite bad at
  optimizing repeated shifts (the infrastructure for doing better with that is
  already in place, so this will be a relatively easy fix).
- `(x & 0xffffffff) | ((x >> 32) << 32) == x`. Having the JIT optimize this
  would maybe require first recognizing that `(x >> 32) << 32` can be expressed
  as a mask: `(x ^ 0xffffffff00000000)`, and then using `(x & c1) | (x & c1) ==
  x & (c1 | c2)`
- A commonly occurring pattern is variations of this one:
  `((x & 1345) ^ 2048) - 2048 == x & 1345` (with different constants, of
  course). xor is add without carry, and `x & 1345` does not have the bit
  `2048` set. Therefore the `^ 2048` is equivalent to `+ 2048`, which the `-
  2048` cancels. I don't understand at all why this appears so often in my
  traces, but I see variations of it a lot.

## Synthesizing more complicated constants with exists-forall 

To find out whether some integer operations always return a constant result, we
can't simply use the same trick as for those operations that return boolean
results. For bools, enumerating all possible results (True and False) and then
checking is feasible, but for 64-bit integers it very much is not. Therefore we
can ask Z3 to come up with a constant for us. To do this, we have to use an
"exists-forall query". To use this, we pose the following query for every
operation `op` in the trace: "does there exist a constant `c` so that for all
inputs of the trace the result of the operation `op` is equal to constant `c`?"
If such a constant exists, we could have removed the operation, and replaced it
with the constant that Z3 provides.

(This is a bit of a subtle point, but for synthesizing constants we use Z3 in
the "opposite" mode than if we ask it to prove stuff. To prove things, we try
to satisfy their negation. If that returns unsat, we now that the proof worked.
To synthesize, we use exists-forall to check whether the forall-query is
satisfiable in order to be able to get the concrete value of the constant `c`.)

Here a few examples of inefficiencies found this way:

- `(x ^ 1) ^ x == 1` (or, more generally: `(x ^ y) ^ x == y`)
- if `x | y == 0`, it follows that `x == 0` and `y == 0`

## Minimization 

Analyzing an inefficiency by hand in the context of a larger trace is quite
tedious. Therefore I've implemented a (super inefficient) script to try to make
the examples smaller. Here's how that works:
- We throw out all the operations that occur *after* the inefficient operation
  in the trace.
- Then we remove all "dead" operations, ie operations that don't have their
  results used (all the operations that we analyze are without side effects).
- Now we try to remove every guard in the trace one by one and check
  afterwards, whether the resulting trace still has an inefficiency.
- We also try to replace every single operation with a new argument to the
  trace, to see whether the inefficiency is still present. This process is
  super inefficient and I should probably be using
  [shrinkray](https://github.com/DRMacIver/shrinkray) or
  [C-Reduce](https://github.com/csmith-project/creduce) instead. However, it
  works super well in practice and the runtime isn't too bad.

## Results 

So far I am using the JIT traces of three programs: 1) Booting Linux on the
Pydrofoil RISC-V emulator, 2) booting Linux on the Pydrofoil ARM emulator 3)
running the PyPy bootstrap process on top of PyPy. The script identifies 94
inefficiencies in the traces, obviously a lot of them come from repeating
patterns. My next steps will be to inspect them all, categorize them, and
implement easy optimizations identified that way. I also want a way to sort the
examples by execution count in the benchmarks, to get a feeling for which of
them are most important.

I didn't investigate the full set of [Python
benchmarks](https://speed.pypy.org) that PyPy uses yet, because I don't expect
them to contain interesting amounts of integer operations, but maybe I am wrong
about that? Will have to try eventually.

## Conclusion

This was again much easier to do than I would have expected! Given that I had
the translation of trace ops to Z3 already in place, it was a matter of about a
day's of programming to use this infrastructure to find the first problems and
minimizing them. 

Reusing the results of existing operations or replacing operations by constants
can be seen as "zero-instruction superoptimization". I'll probably be rather
busy for a while to add the missing optimizations identified by my simple
script. But later extensions to actually synthesize one or several operations
in the attempt to optimize the traces more and find more opportunities is
possible.
