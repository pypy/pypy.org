<!--
.. title: Finding Complicated Missing JIT Compiler Optimizations with Z3
.. slug: finding-missing-optimizations-z3
.. date: 2024-07-07 19:14:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: CF Bolz-Tereick
-->

In last weeks post I've described how to use Z3 to find simple local peephole
optimization patterns to for the integer operations in PyPy's JIT. An example
is `int_and(x, 0) -> 0`. The post ended by discussing problems:

- combinatorial explosion
- non-minimal examples
- how do we know that we even care about the patterns that it finds?

In this post I want to discuss a different method:

- start from real programs that we care about (e.g. benchmarks)
- take their traces, ignore all the non-integer operations
- translate the traces into big Z3 formulas, operation by operation
- use Z3 to identify inefficiens in those concrete traces
- minimize the inefficient programs by removing as many operations as possible

that way we don't have to generate all possible sequences of ir operations up
to a certain size, and we also get optimizations that we care about, because
the patterns come from real programs

post will be more high-level and describe the general approach, but not go
through the implementation in detail.

## Background 

PyPy's JIT has historically always focused almost exclusively on the typical
inefficiencies of Python programs, such as removing boxing, run-time type
feedback, speculation type-specializing collections, etc. However, in the last
two years I have applied the JIT also to a very different domain, that of CPU
emulation, in the experimental [Pydrofoil](https://docs.pydrofoil.org) project
(supports RISC-V and ARM by now). For Pydrofoil, the performance of integer
operations is significantly more important than for "normal" Python code, which
is why I've become much more interested in optimizing integer operations. The
simple integer operation rewrites of the last post were all implemented long
ago, and so were a lot of more complicated ones. But there surely are a lot of
them missing, compared to mature compilers.

Finding missing optimizations is quite hard to do manually, because it involves
carefully staring at huge concrete traces of programs that we care about. So
ideally we want to automate the problem. To make sure that we care about the
optimizations that we find, we start from the traces of benchmarks that are
interesting, such as booting Linux on the ARM and RISC-V emulators.


## General Recipe for Finding Missing Optimizations 

We want to use it to find
missing integer optimizations in the PyPy JIT. The general approach is to first
collect a bunch of traces of integer heavy programs. Then we encode the integer
operations in the traces into Z3 formulas and use different Z3 queries to
identify inefficiencies in the traces. Once we found an inefficiency, we try to
minimize the trace to the smallest trace that we can get that still shows an
inefficiency to make it easier to understand. Then we inspect the minimized
cases manually and (if possible) try to implement the missing optimizations.
I'll write about each of these steps in turn.

## Encoding Traces as Z3 formulas 

The last blog post already contained the code to encode individual trace
operations into Z3 formulas, so we don't need to repeat that here. To encode
traces of operations we introduce a Z3 variable for every operation in the
trace and then call the `z3_expression` function for every single one of the
operations in the trace.

For example, for the following trace:

```
[i1]
i2 = uint_rshift(i1, 32)
i3 = int_and(i2, 65535)
i4 = uint_rshift(i1, 48)
i5 = int_lshift(i4, 16)
i6 = int_or(i5, i3)
jump(i6, i2) # equal
```

We would get the Z3 formula:

```
z3.And(i2 == LShR(i1, 32),
       i3 == i2 & 65535,
       i4 == LShR(i1, 48),
       i5 == i4 << 16)
```

## Identifying constant booleans with Z3

The very simplest thing we can try to find inefficient parts of the traces is
to first focus on boolean variables. For every boolean variable in the trace we
can ask Z3 to prove that this variable must be always True or always False.
Most of the time, neither of these proofs will succeed. But if Z3 manages to
prove one of them, we know have found an ineffiency: instead of computing the
boolean result (eg by executing a comparison) we could have replaced the
operation with the corresponding constant.

Here's an example of an inefficiency found that way: if `x < y` and `y < z` are
both true, PyPy's JIT could conclude that `x < z` must also
be true. However, currently the JIT cannot make that conclusion because the JIT
only reasons about the concrete ranges (lower and upper bounds) for every
integer variable, but it has no way to remember anything about relationships
between different variables. This kind of reasoning would quite often be useful
to remove list/string bounds checks. Here's a [talk about how LLVM does
this](https://www.youtube.com/watch?app=desktop&v=1hm5ZVmBEvo) (but it might be
too heavyweight for a JIT setting).

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
  2048` cancels. More generally, if `a & b == 0`, then `a + b == a | b == a ^
  b`. I don't understand at all why this appears so often in my traces, but I
  see variations of it a lot. LLVM can optimize this, but [GCC
  can't](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=115829), thanks to
  [Andrew Pinski for filing the
  bug](https://hachyderm.io/@pinskia/112752641328799157)!

## Synthesizing more complicated constants with exists-forall 

To find out whether some integer operations always return a constant result, we
can't simply use the same trick as for those operations that return boolean
results. Like in the last post, we can use `z3.ForAll` to find out whether Z3
can synthesize constants for us, for the result of an operation in ints
context. If such a constant exists, we could have removed the operation, and
replaced it with the constant that Z3 provides.

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
  results used (all the operations that we can analyze with Z3 are without side
  effects).
- Now we try to remove every guard in the trace one by one and check
  afterwards, whether the resulting trace still has an inefficiency.
- We also try to replace every single operation with a new argument to the
  trace, to see whether the inefficiency is still present.

 The minimization process is super inefficient and I should probably be using
 [shrinkray](https://github.com/DRMacIver/shrinkray) or
 [C-Reduce](https://github.com/csmith-project/creduce) instead. However, it
 seems to work well in practice and the runtime isn't too bad.

## Results 

So far I am using the JIT traces of three programs: 1) Booting Linux on the
Pydrofoil RISC-V emulator, 2) booting Linux on the Pydrofoil ARM emulator 3)
running the PyPy bootstrap process on top of PyPy. The script identifies 94
inefficiencies in the traces, obviously a lot of them come from repeating
patterns. My next steps will be to manually inspect them all, categorize them, and
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
in the attempt to optimize the traces more and find more opportunities should
be possible.
