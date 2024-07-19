<!--
.. title: Mining JIT traces for missing optimizations with Z3
.. slug: mining-jit-traces-missing-optimizations-z3
.. date: 2024-07-19 19:14:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: CF Bolz-Tereick
-->

In my last post I've described [how to use Z3 to find simple local peephole
optimization patterns](finding-simple-rewrite-rules-jit-z3.html)
for the integer operations in PyPy's JIT. An example is `int_and(x, 0) ->
0`. In this post I want to scale up the problem of identifying possible
optimizations to much bigger instruction sequences, also using Z3. For that, I
am starting with the JIT traces of **real benchmarks**, after they have been
optimized by the optimizer of PyPy's JIT. Then we can ask Z3 to find
inefficient integer operations in those traces.

Starting from the optimized traces of real programs has some big
advantages over the "classical" superoptimization approach of generating and
then trying all possible sequences of instructions. It avoids the
combinatorical explosion that happens with the latter approach. Also, starting
from the traces of benchmarks or (even better) actual programs makes sure that
we actually care about the missing optimizations
that are found in this way. And because the traces are analyzed after they have
been optimized by PyPy's optimizer, we only get reports for *missing*
optimizations, that the JIT isn't able to do (yet).

The techniques and experiments I describe in this post are again the result of
a bunch of discussions with John Regehr at a conference a few weeks ago, as
well as reading his blog posts and papers. Thanks John!


## High-Level Approach

The approach that I took works as follows:

- Run benchmarks or other interesting programs and then dump the IR of the JIT
  traces into a file. The traces have at that point been already optimized by
  the PyPy JIT's optimizer.
- For every trace, ignore all the operations on non-integer variables.
- Translate every integer operation into a Z3 formula.
- For every operation, use Z3 to find out whether the operation is redundant
  (how that is done is described below).
- If the operation is redundant, the trace is less efficient than it could have
  been, because the optimizer could also have removed the operation. Report the
  inefficiency.
- Minimize the inefficient programs by removing as many operations as possible
  to make the problem easier to understand.

In the post I will describe the details and show some pseudocode of the
approach. I'll also make the proper code public eventually (but it needs a
healthy dose of cleanups first).

## Dumping PyPy Traces

PyPy will write its JIT traces into the file `out` if the environment variable
[`PYPYLOG`](https://doc.pypy.org/en/latest/man/pypy.1.html) is set as follows:

```
PYPYLOG=jit-log-opt:out
```

## Encoding Traces as Z3 formulas

The last blog post already contained the code to encode the results of
individual trace operations into Z3 formulas, so we don't need to repeat that
here. To encode traces of operations we introduce a Z3 variable for every
operation in the trace and then call the `z3_expression` function for every
single one of the operations in the trace.

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

Usually we won't ask for the formula of the whole trace at once. Instead we go
through the trace operation by operation and try to find inefficiencies in the
current one we are looking at. Roughly like this (pseudo-)code:

```python
def newvar(name):
    return z3.BitVec(name, INTEGER_WIDTH)

def find_inefficiencies(trace):
    solver = z3.Solver()
    var_to_z3var = {}
    for input_argument in trace.inputargs:
        var_to_z3var[input_argument] = newz3var(input_argument)
    for op in trace:
        var_to_z3var[op] = z3resultvar = newz3var(op.resultvarname)
        arg0 = op.args[0]
        z3arg0 = var_to_z3var[arg0]
        if len(op.args) == 2:
            arg1 = op.args[1]
            z3arg1 = var_to_z3var[arg1]
        else:
            z3arg1 = None
        res, valid_if = z3_expression(op.name, z3arg0, z3arg1)
        # checking for inefficiencies, see the next sections
        ...
        if ...:
            return "inefficient", op

        # not inefficient, assert op into the solver and continue with the next op
        solver.add(z3resultvar == res)
    return None # no inefficiency found
```



## Identifying constant booleans with Z3

To get started finding inefficiencies in a trace, we can
first focus on boolean variables. For every operation in the trace that
returns a bool we can ask Z3 to prove that this variable must be always True or
always False. Most of the time, neither of these proofs will succeed. But if Z3
manages to prove one of them, we know have found an ineffiency: instead of
computing the boolean result (eg by executing a comparison) the JIT's optimizer
could have replaced the operation with the corresponding boolean constant.

Here's an example of an inefficiency found that way: if `x < y` and `y < z` are
both true, PyPy's JIT could conclude that `x < z` must also
be true. However, currently the JIT cannot make that conclusion because it
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

Here's pseudo-code for how to implement checking boolean operations for
inefficiencies:

```python
def find_inefficiencies(trace):
    ...
    for op in trace:
        ...
        res, valid_if = z3_expression(op.name, z3arg0, z3arg1)
        # check for boolean constant result
        if op.has_boolean_result():
            if prove(solver, res == 0):
                return "inefficient", op, 0
            if prove(solver, res == 1):
                return "inefficient", op, 1
        # checking for other inefficiencies, see the next sections
        ...

        # not inefficient, add op to the solver and continue with the next op
        solver.add(z3resultvar == res)
    return None # no inefficiency found
```


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
  2048` cancels. More generally, if `a & b == 0`, then `a + b == a | b == a ^ b`.
  I don't understand at all why this appears so often in the traces, but I
  see variations of it a lot. LLVM can optimize this, but [GCC
  can't](https://gcc.gnu.org/bugzilla/show_bug.cgi?id=115829), thanks to
  [Andrew Pinski for filing the
  bug](https://hachyderm.io/@pinskia/112752641328799157)!


And here's some implementation pseudo-code again:

```python
def find_inefficiencies(trace):
    ...
    for op in trace:
        ...
        res, valid_if = z3_expression(op.name, z3arg0, z3arg1)
        # check for boolean constant result
        ...
        # searching for redundant operations
        for previous_op in trace:
            if previous_op is op:
                break # done, reached the current op
            previous_op_z3var = var_to_z3var[previous_op]
            if prove(solver, previous_op_z3var == res):
                return "inefficient", op, previous_op
        ...
        # more code here later
        ...

        # not inefficient, add op to the solver and continue with the next op
        solver.add(z3resultvar == res)
    return None # no inefficiency found
```

## Synthesizing more complicated constants with exists-forall

To find out whether some integer operations always return a constant result, we
can't simply use the same trick as for those operations that return boolean
results, because enumerating 2⁶⁴ possible constants and checking them all
would take too long. Like in the last post, we can use `z3.ForAll` to find out
whether Z3 can synthesize a constant for the result of an operation for us.
If such a constant exists, the JIT could have removed the operation,
and replaced it with the constant that Z3 provides.

Here a few examples of inefficiencies found this way:

- `(x ^ 1) ^ x == 1` (or, more generally: `(x ^ y) ^ x == y`)
- if `x | y == 0`, it follows that `x == 0` and `y == 0`
- if `x != MAXINT`, then `x + 1 > x`

Implementing this is actually slightly annoying. The `solver.add` calls for
non-inefficient ops add assertions to the solver, which are now confusing the
`z3.ForAll` query. We could remove all assertion from the solver, then do the
`ForAll` query, then add the assertions back. What I ended doing instead was
instantiating a second solver object that I'm using for the `ForAll` queries,
that remains empty the whole time.

```python
def find_inefficiencies(trace):
    solver = z3.Solver()
    empty_solver = z3.Solver()
    var_to_z3var = {}
    ...
    for op in trace:
        ...
        res, valid_if = z3_expression(op.name, z3arg0, z3arg1)
        # check for boolean constant result
        ...
        # searching for redundant operations
        ...
        # checking for constant results
        constvar = z3.BitVec('find_const', INTEGER_WIDTH)
        condition = z3.ForAll(
            var_to_z3var.values(),
            z3.Implies(
                *solver.assertions(),
                expr == constvar
            )
        )
        if empty_solver.check(condition) == z3.sat:
            model = empty_solver.model()
            const = model[constvar].as_signed_long()
            return "inefficient", op, const

        # not inefficient, add op to the solver and continue with the next op
        solver.add(z3resultvar == res)
    return None # no inefficiency found
```

## Minimization

Analyzing an inefficiency by hand in the context of a larger trace is quite
tedious. Therefore I've implemented a (super inefficient) script to try to make
the examples smaller. Here's how that works:

- First throw out all the operations that occur *after* the inefficient operation
  in the trace.
- Then we remove all "dead" operations, ie operations that don't have their
  results used (all the operations that we can analyze with Z3 are without side
  effects).
- Now we try to remove every guard in the trace one by one and check
  afterwards, whether the resulting trace still has an inefficiency.
- We also try to replace every single operation with a new argument to the
  trace, to see whether the inefficiency is still present.

 The minimization process is sort of inefficient and I should probably be using
 [shrinkray](https://github.com/DRMacIver/shrinkray) or
 [C-Reduce](https://github.com/csmith-project/creduce) instead. However, it
 seems to work well in practice and the runtime isn't too bad.

## Results

So far I am using the JIT traces of three programs: 1) Booting Linux on the
[Pydrofoil](https://docs.pydrofoil.org) RISC-V emulator, 2) booting Linux on the Pydrofoil ARM emulator, and 3)
running the PyPy bootstrap process on top of PyPy.

I picked these programs because most Python programs don't contain interesting
amounts of integer operations, and the traces of the emulators
contain a lot of them. I also used the bootstrap process because I still wanted
to try a big Python program and personally care about the runtime of this
program a lot.

The script identifies 94
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

Finding inefficiencies in traces with Z3 is significantly less
annoying and also less error-prone than just manually inspecting traces and
trying to spot optimization opportunities.


## Random Notes and Sources

Again, John's blog posts:

- [Let’s Work on an LLVM Superoptimizer](https://blog.regehr.org/archives/1109)
- [Early Superoptimizer Results](https://blog.regehr.org/archives/1146)
- [A Few Synthesizing Superoptimizer Results](https://blog.regehr.org/archives/1252)
- [Synthesizing Constants](https://blog.regehr.org/archives/1636)

and papers:

- [A Synthesizing Superoptimizer](https://arxiv.org/pdf/1711.04422)
- [Hydra: Generalizing Peephole Optimizations with Program Synthesis](https://dl.acm.org/doi/pdf/10.1145/3649837)

I remembered recently that I had seen the approach of optimizing the traces of
a tracing JIT with Z3 a long time ago, as part of the (now long dead, I think)
[SPUR
project](https://web.archive.org/web/20160304055149/http://research.microsoft.com/en-us/projects/spur/).
There's a [workshop
paper](https://web.archive.org/web/20161029162737/http://csl.stanford.edu/~christos/pldi2010.fit/tillmann.provers4jit.pdf)
from 2010 about this. SPUR was trying to use Z3 built into the actual JIT (as
opposed to using Z3 only to find places where the regular optimizers could be
improved). In addition to bitvectors, SPUR also used the Z3 support for arrays
to model the C# heap and remove redundant stores. This is still another future
extension for all the Z3 work I've been doing in the context of the PyPy JIT.
