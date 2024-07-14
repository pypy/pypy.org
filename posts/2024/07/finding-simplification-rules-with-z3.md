<!--
.. title: Finding Simple Rewrite Rules for the JIT with Z3
.. slug: finding-simple-rewrite-rules-jit-z3
.. date: 2024-07-12 19:14:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. has_math: True
.. author: CF Bolz-Tereick
-->

In June I was at the [PLDI conference](https://pldi24.sigplan.org/) in
Copenhagen to present a [paper](https://dl.acm.org/doi/10.1145/3652588.3663316)
I co-authored with [Max Bernstein](https://bernsteinbear.com/). I also finally
met [John Regehr](https://blog.regehr.org/), who I'd been talking on social
media for ages but had never met. John has been working on compiler correctness
and better techniques for building compilers and optimizers since a very long
time. The blog post [Finding JIT Optimizer Bugs using SMT Solvers and
Fuzzing](https://www.pypy.org/posts/2022/12/jit-bug-finding-smt-fuzzing.html)
was heavily inspired by this work. We talked a lot about his and his groups
work on using Z3 for
[superoptimization](https://en.wikipedia.org/wiki/Superoptimization) and for
finding missing optimizations. I have applied some of the things John told me
about to the traces of PyPy's JIT, and wanted to blog about that. However, my
draft felt quite hard to understand. Therefore I have now written this current
post, to at least try to provide a somewhat gentler on-ramp to the topic.

In *this* post we will use the Python-API to Z3 to find local peephole rewrite
rules for the operations in the intermediate representation of PyPy's tracing
JIT. The code for this is simple enough that we can go through all of it.

The PyPy JIT produces traces of machine level instructions, which are optimized
and then turned into machine code. The optimizer uses a number of approaches to
make the traces more efficient. For integer operations it applies a number of
arithmetic simplification rules rules, for example `int_add(x, 0) -> x`. When
implementing these rules in the JIT there are **two problems**: How do we know
that the rules are correct? And how do we know that we haven't forgotten any
rules? We'll try to answer both of these, but the first one in particular.

We'll be using Z3, a satisfiability module theories (SMT) solver which has good
bitvector support and most importantly an excellent Python API. We can use the
solver to reason about bitvectors, which are how we will model machine
integers.

To find rewrite rules, we will consider the binary operations (i.e. those
taking two arguments) in PyPy traces that take and produce integers. The
completely general form `op(x, y)` is not simplifiable on its own. But if
either `x == y`
or if one of the arguments is a constant, we can potentially simplify the
operation into a simpler form. The results are either the variable `x`, or a
(potentially different) constant. We'll ignore constant-folding where both
arguments of the binary operation are constants. The possible results for a
simplifiable binary operation are the variable `x` or another constant. This
leaves the following patterns as possibilities:

- `op(x, x) == x`
- `op(x, x) == c1`
- `op(x, c1) == x`
- `op(c1, x) == x`
- `op(x, c1) == c2`
- `op(c1, x) == c2`

Our approach will be to take every single supported binary integer operation,
instantiate all of these patterns, and try to ask Z3 whether the resulting
simplification is valid for all values of `x`.

## Quick intro to the Z3 Python-API

Here's a terminal session showing the use of the Z3 Python API:


```python-console
>>>> import z3
>>>> # construct a Z3 bitvector variable of width 8, with name x:
>>>> x = z3.BitVec('x', 8)
>>>> # construct a more complicated formula by using operator overloading:
>>>> x + x
x + x
>>>> x + 1
x + 1
```

Z3 checks the "satisfiability" of a formula. This means that it tries to find
an example set of concrete values for the variables that occur in a formula,
such that the formula becomes true. Examples:

```python-console
>>>> solver = z3.Solver()
>>>> solver.check(x * x == 3)
unsat
>>>> # meaning no x fulfils this property
>>>>
>>>> solver.check(x * x == 9)
sat
>>>> model = solver.model()
>>>> model
[x = 253]
>>>> model[x].as_signed_long()
-3
>>>> # 253 is the same as -3 in two's complement arithmetic with 8 bits
```

In order to use Z3 to prove something, we can ask Z3 to find counterexamples
for the statement, meaning concrete values that would make the negation of the
statement true:

```python-console
>>>> solver.check(z3.Not(x ^ -1 == ~x))
unsat
```

The result `unsat` means that we just proved that `x ^ -1 == ~x` is true for
all `x`, because there is no value for `x` that makes `not (x ^ -1 == ~x)`
true (this works because -1 has all the bits set).

If we try to prove something incorrect in this way, the following happens:

```python-console
>>>> solver.check(z3.Not(x ^ -1 == x))
sat
```

`sat` shows that `x ^ -1 == x` is (unsurprisingly) not always true, and we can
ask for a counterexample:

```python-console
>>>> solver.model()
[x = 0]
```

This way of proving this works because the `check` calls try to solve an
(implicit) "exists" quantifier, over all the Z3 variables used in the formula.
`check` will either return `z3.unsat`, which means that no concrete values make
the formula true; or `z3.sat`, which means that you can get some concrete
values that make the formula true by calling `solver.model()`.

In math terms we prove things using `check` by de-Morgan's rules for quantifiers:

$$ \lnot \exists x: \lnot f(x) \implies \forall x: f(x) $$

Now that we've seen the basics of using the Z3 API on a few small examples,
we'll use it in a bigger program.

## Encoding the integer operations of RPython's JIT into Z3 formulas

Now we'll use the API to reason about the integer operations of the PyPy JIT
intermediate representation (IR). The binary integer operations are:

```python
opnames2 = [
"int_add",
"int_sub",
"int_mul",
"int_and",
"int_or",
"int_xor",
"int_eq",
"int_ne",
"int_lt",
"int_le",
"int_gt",
"int_ge",
"uint_lt",
"uint_le",
"uint_gt",
"uint_ge",
"int_lshift",
"int_rshift",
"uint_rshift",
"uint_mul_high",
"int_pydiv",
"int_pymod",
]
```
There's not much special about the integer operations. Like in LLVM, most of
them are signedness-independent: `int_add`, `int_sub`, `int_mul`, ... work
correctly for unsigned integers but also for
[two's-complement](https://en.wikipedia.org/wiki/Two%27s_complement) signed
integers. Exceptions for that are order comparisons like `int_lt` etc. for
which we have unsigned variants `uint_lt` etc. All operations that produce a
boolean result return a full-width integer `0` or `1` (the PyPy JIT supports
only word-sized integers in its intermediate representation)

In order to reason about the IR operations, some ground work:

```python
import z3

INTEGER_WIDTH = 64
solver = z3.Solver()
solver.set("timeout", 10000) # milliseconds, ie 10s
xvar = z3.BitVec('x', INTEGER_WIDTH)
constvar = z3.BitVec('const', INTEGER_WIDTH)
constvar2 = z3.BitVec('const2', INTEGER_WIDTH)
TRUEBV = z3.BitVecVal(1, INTEGER_WIDTH)
FALSEBV = z3.BitVecVal(0, INTEGER_WIDTH)
```

And here's the a function to turn an integer IR operation of PyPy's JIT into Z3
formulas:

```python
def z3_expression(opname, arg0, arg1=None):
    """ computes a tuple of (result, valid_if) of Z3 formulas. `result` is the
    formula representing the result of the operation, given argument formulas
    arg0 and arg1. `valid_if` is a pre-condition that must be true for the
    result to be meaningful. """
    result = None
    valid_if = True # the precondition is mostly True, with few exceptions
    if opname == "int_add":
        result = arg0 + arg1
    elif opname == "int_sub":
        result = arg0 - arg1
    elif opname == "int_mul":
        result = arg0 * arg1
    elif opname == "int_and":
        result = arg0 & arg1
    elif opname == "int_or":
        result = arg0 | arg1
    elif opname == "int_xor":
        result = arg0 ^ arg1
    elif opname == "int_eq":
        result = cond(arg0 == arg1)
    elif opname == "int_ne":
        result = cond(arg0 != arg1)
    elif opname == "int_lt":
        result = cond(arg0 < arg1)
    elif opname == "int_le":
        result = cond(arg0 <= arg1)
    elif opname == "int_gt":
        result = cond(arg0 > arg1)
    elif opname == "int_ge":
        result = cond(arg0 >= arg1)
    elif opname == "uint_lt":
        result = cond(z3.ULT(arg0, arg1))
    elif opname == "uint_le":
        result = cond(z3.ULE(arg0, arg1))
    elif opname == "uint_gt":
        result = cond(z3.UGT(arg0, arg1))
    elif opname == "uint_ge":
        result = cond(z3.UGE(arg0, arg1))
    elif opname == "int_lshift":
        result = arg0 << arg1
        valid_if = z3.And(arg1 >= 0, arg1 < INTEGER_WIDTH)
    elif opname == "int_rshift":
        result = arg0 << arg1
        valid_if = z3.And(arg1 >= 0, arg1 < INTEGER_WIDTH)
    elif opname == "uint_rshift":
        result = z3.LShR(arg0, arg1)
        valid_if = z3.And(arg1 >= 0, arg1 < INTEGER_WIDTH)
    elif opname == "uint_mul_high":
        # zero-extend args to 2*INTEGER_WIDTH bit, then multiply and extract
        # highest INTEGER_WIDTH bits
        zarg0 = z3.ZeroExt(INTEGER_WIDTH, arg0)
        zarg1 = z3.ZeroExt(INTEGER_WIDTH, arg1)
        result = z3.Extract(INTEGER_WIDTH * 2 - 1, INTEGER_WIDTH, zarg0 * zarg1)
    elif opname == "int_pydiv":
        valid_if = arg1 != 0
        r = arg0 / arg1
        psubx = r * arg1 - arg0
        result = r + (z3.If(arg1 < 0, psubx, -psubx) >> (INTEGER_WIDTH - 1))
    elif opname == "int_pymod":
        valid_if = arg1 != 0
        r = arg0 % arg1
        result = r + (arg1 & z3.If(arg1 < 0, -r, r) >> (INTEGER_WIDTH - 1))
    elif opname == "int_is_true":
        result = cond(arg0 != FALSEBV)
    elif opname == "int_is_zero":
        result = cond(arg0 == FALSEBV)
    elif opname == "int_neg":
        result = -arg0
    elif opname == "int_invert":
        result = ~arg0
    else:
        assert 0, "unknown operation " + opname
    return result, valid_if

def cond(z3expr):
    """ helper function to turn a Z3 boolean result z3expr into a 1 or 0
    bitvector, using z3.If """
    return z3.If(z3expr, TRUEBV, FALSEBV)
```

We map the semantics of a PyPy JIT operation to Z3 with the `z3_expression`
function. It takes the name of a JIT operation and its two (or one) arguments
into a pair of Z3 formulas, `result` and `valid_if`. The resulting formulas are
constructed with the operator overloading of Z3 variables/formulas.

The first element `result` of the result of `z3_expression` represents the result
of performing the operation. `valid_if` is a bool that represents a condition that
needs to be `True` in order for the result of the operation to be defined. E.g.
`int_pydiv(a, b)` is only valid if `b != 0`. Most operations are always valid,
so they return `True` as that condition (we'll ignore `valid_if` for a bit, but it
will become more relevant further down in the post).

We can define a helper function to prove things by finding counterexamples:

```python
def prove(cond):
    """ Try to prove a condition cond by searching for counterexamples of its negation. """
    z3res = solver.check(z3.Not(cond))
    if z3res == z3.unsat:
        return True
    elif z3res == z3.unknown: # eg on timeout
        return False
    elif z3res == z3.sat:
        return False
    assert 0, "should be unreachable"
```

## Finding rewrite rules

Now we can start finding our first rewrite rules, following the first pattern
`op(x, x) -> x`. We do this by iterating over all the supported binary
operation names, getting the z3 expression for `op(x, x)` and then asking Z3 to
prove `op(x, x) == x`.

```python

for opname in opnames2:
    result, valid_if = z3_expression(opname, xvar, xvar)
    if prove(result == xvar):
        print(f"{opname}(x, x) -> x, {result}")
```

This yields the simplifications:

```
int_and(x, x) -> x
int_or(x, x) -> x
```


## Synthesizing constants

Supporting the next patterns is harder: `op(x, x) == c1`, `op(x, c1) == x`, and
`op(c1, x) == x`. We don't know which constants to pick to try to get Z3 to
prove the equality. We could iterate over common constants like `0`, `1`,
`MAXINT`, etc, or even over all the 256 values for a bitvector of length 8.
However, we will instead ask Z3 to find the constants for us too.

This can be done by using quantifiers, in this case `z3.ForAll`. The query we
pose to Z3 is "does there exist a constant `c1` such that for all `x` the
following is true: `op(x, c1) == x`? Note that the constant `c1` is not
necessarily unique, there could be many of them. We generate several matching
constant, and add that they must be different to the condition of the second
and further queries.

We can express this in a helper function:

```python
def find_constant(z3expr, number_of_results=5):
    condition = z3.ForAll(
        [xvar],
        z3expr
    )
    for i in range(number_of_results):
        checkres = solver.check(condition)
        if checkres == z3.sat:
            # if a solver check succeeds, we can ask for a model, which is
            # concrete values for the variables constvar
            model = solver.model()
            const = model[constvar].as_signed_long()
            yield const
            # make sure we don't generate the same constant again on the
            # next call
            condition = z3.And(constvar != const, condition)
        else:
            # no (more) constants found
            break
```

We can use this new function for the three mentioned patterns:

```python
# try to find constants for op(x, x) == c
for opname in opnames2:
    result, valid_if = z3_expression(opname, xvar, xvar)
    for const in find_constant(result == constvar):
        print(f"{opname}(x, x) -> {const}")
# try to find constants for op(x, c) == x and op(c, x) == x
for opname in opnames2:
    result, valid_if = z3_expression(opname, xvar, constvar)
    for const in find_constant(result == xvar):
        print(f"{opname}(x, {const}) -> x")
    result, valid_if = z3_expression(opname, constvar, xvar)
    for const in find_constant(result == xvar):
        print(f"{opname}({const}, x) -> x")
# this code is not quite correct, we'll correct it later
```


Together this yields the following new simplifications:

```
# careful, these are not all correct!
int_sub(x, x) -> 0
int_xor(x, x) -> 0
int_eq(x, x) -> 1
int_ne(x, x) -> 0
int_lt(x, x) -> 0
int_le(x, x) -> 1
int_gt(x, x) -> 0
int_ge(x, x) -> 1
uint_lt(x, x) -> 0
uint_le(x, x) -> 1
uint_gt(x, x) -> 0
uint_ge(x, x) -> 1
uint_rshift(x, x) -> 0
int_pymod(x, x) -> 0
int_add(x, 0) -> x
int_add(0, x) -> x
int_sub(x, 0) -> x
int_mul(x, 1) -> x
int_mul(1, x) -> x
int_and(x, -1) -> x
int_and(-1, x) -> x
int_or(x, 0) -> x
int_or(0, x) -> x
int_xor(x, 0) -> x
int_xor(0, x) -> x
int_lshift(x, 0) -> x
int_rshift(x, 0) -> x
uint_rshift(x, 0) -> x
int_pydiv(x, 1) -> x
int_pymod(x, 0) -> x
```

Most of these look good at first glance, but the last one reveals a problem:
we've been ignoring the `valid_if` expression up to now. We can stop doing that by
changing the code like this, which adds `z3.And(valid_if, ...)` to the argument of
the calls to `find_constant`:

```python
# try to find constants for op(x, x) == c, op(x, c) == x and op(c, x) == x
for opname in opnames2:
    result, valid_if = z3_expression(opname, xvar, xvar)
    for const in find_constant(z3.And(valid_if, result == constvar)):
        print(f"{opname}(x, x) -> {const}")
# try to find constants for op(x, c) == x and op(c, x) == x
for opname in opnames2:
    result, valid_if = z3_expression(opname, xvar, constvar)
    for const in find_constant(z3.And(result == xvar, valid_if)):
        print(f"{opname}(x, {const}) -> x")
    result, valid_if = z3_expression(opname, constvar, xvar)
    for const in find_constant(z3.And(result == xvar, valid_if)):
        print(f"{opname}({const}, x) -> x")
```

And we get this list instead:

```
int_sub(x, x) -> 0
int_xor(x, x) -> 0
int_eq(x, x) -> 1
int_ne(x, x) -> 0
int_lt(x, x) -> 0
int_le(x, x) -> 1
int_gt(x, x) -> 0
int_ge(x, x) -> 1
uint_lt(x, x) -> 0
uint_le(x, x) -> 1
uint_gt(x, x) -> 0
uint_ge(x, x) -> 1
int_add(x, 0) -> x
int_add(0, x) -> x
int_sub(x, 0) -> x
int_mul(x, 1) -> x
int_mul(1, x) -> x
int_and(x, -1) -> x
int_and(-1, x) -> x
int_or(x, 0) -> x
int_or(0, x) -> x
int_xor(x, 0) -> x
int_xor(0, x) -> x
int_lshift(x, 0) -> x
int_rshift(x, 0) -> x
uint_rshift(x, 0) -> x
int_pydiv(x, 1) -> x
```

## Synthesizing two constants

For the patterns `op(x, c1) == c2` and `op(c1, x) == c2` we need to synthesize
two constants. We can again write a helper method for that:

```python
def find_2consts(z3expr, number_of_results=5):
    condition = z3.ForAll(
        [xvar],
        z3expr
    )
    for i in range(number_of_results):
        checkres = solver.check(condition)
        if checkres == z3.sat:
            model = solver.model()
            const = model[constvar].as_signed_long()
            const2 = model[constvar2].as_signed_long()
            yield const, const2
            condition = z3.And(z3.Or(constvar != const, constvar2 != const2), condition)
        else:
            return
```

And then use it like this:

```python
for opname in opnames2:
    # try to find constants c1, c2 such that op(c1, x) -> c2
    result, valid_if = z3_expression(opname, constvar, xvar)
    consts = find_2consts(z3.And(valid_if, result == constvar2))
    for const, const2 in consts:
        print(f"{opname}({const}, x) -> {const2}")
    # try to find constants c1, c2 such that op(x, c1) -> c2
    result, valid_if = z3_expression(opname, xvar, constvar)
    consts = find_2consts(z3.And(valid_if, result == constvar2))
    for const, const2 in consts:
        print("%s(x, %s) -> %s" % (opname, const, const2))
```

Which yields some straightforward simplifications:

```
int_mul(0, x) -> 0
int_mul(x, 0) -> 0
int_and(0, x) -> 0
int_and(x, 0) -> 0
uint_lt(x, 0) -> 0
uint_le(0, x) -> 1
uint_gt(0, x) -> 0
uint_ge(x, 0) -> 1
int_lshift(0, x) -> 0
int_rshift(0, x) -> 0
uint_rshift(0, x) -> 0
uint_mul_high(0, x) -> 0
uint_mul_high(1, x) -> 0
uint_mul_high(x, 0) -> 0
uint_mul_high(x, 1) -> 0
int_pymod(x, 1) -> 0
int_pymod(x, -1) -> 0
```
A few require a bit more thinking:

```
int_or(-1, x) -> -1
int_or(x, -1) -> -1
```

The are true because in two's complement, `-1` has all bits set.

The following ones require recognizing that `-9223372036854775808 == -2**63` is
the most negative signed 64-bit integer, and `9223372036854775807 == 2 ** 63 -
1` is the most positive one:

```
int_lt(9223372036854775807, x) -> 0
int_lt(x, -9223372036854775808) -> 0
int_le(-9223372036854775808, x) -> 1
int_le(x, 9223372036854775807) -> 1
int_gt(-9223372036854775808, x) -> 0
int_gt(x, 9223372036854775807) -> 0
int_ge(9223372036854775807, x) -> 1
int_ge(x, -9223372036854775808) -> 1
```

The following ones are true because the bitpattern for `-1` is the largest
unsigned number:

```
uint_lt(-1, x) -> 0
uint_le(x, -1) -> 1
uint_gt(x, -1) -> 0
uint_ge(-1, x) -> 1
```

## Strength Reductions

All the patterns so far only had a variable or a constant on the target of the
rewrite. We can also use the machinery to do strengh-reductions where we
generate a single-argument operation `op1(x)` for input operations `op(x, c1)`
or `op(c1, x)`. To achieve this, we try all combinations of binary and unary
operations. (We won't consider strength reductions where a binary operation
gets turned into a "cheaper" other binary operation here.)

```python
opnames1 = [
"int_is_true",
"int_is_zero",
"int_neg",
"int_invert",
]

for opname in opnames2:
    for opname1 in opnames1:
        result, valid_if = z3_expression(opname, xvar, constvar)
        # try to find a constant op(x, c) == g(x)
        result1, valid_if1 = z3_expression(opname1, xvar)
        consts = find_constant(z3.And(valid_if, valid_if1, result == result1))
        for const in consts:
            print(f"{opname}(x, {const}) -> {opname1}(x)")

        # try to find a constant op(c, x) == g(x)
        result, valid_if = z3_expression(opname, constvar, xvar)
        result1, valid_if1 = z3_expression(opname1, xvar)
        consts = find_constant(z3.And(valid_if, valid_if1, result == result1))
        for const in consts:
            print(f"{opname}({const}, x) -> {opname1}(x)")
```

Which yields the following new simplifications:

```
int_sub(0, x) -> int_neg(x)
int_sub(-1, x) -> int_invert(x)
int_mul(x, -1) -> int_neg(x)
int_mul(-1, x) -> int_neg(x)
int_xor(x, -1) -> int_invert(x)
int_xor(-1, x) -> int_invert(x)
int_eq(x, 0) -> int_is_zero(x)
int_eq(0, x) -> int_is_zero(x)
int_ne(x, 0) -> int_is_true(x)
int_ne(0, x) -> int_is_true(x)
uint_lt(0, x) -> int_is_true(x)
uint_lt(x, 1) -> int_is_zero(x)
uint_le(1, x) -> int_is_true(x)
uint_le(x, 0) -> int_is_zero(x)
uint_gt(x, 0) -> int_is_true(x)
uint_gt(1, x) -> int_is_zero(x)
uint_ge(x, 1) -> int_is_true(x)
uint_ge(0, x) -> int_is_zero(x)
int_pydiv(x, -1) -> int_neg(x)
```


## Conclusions

With not very little code we managed to generate a whole lot of local
simplifications for integer operations in the IR of PyPy's JIT. The rules
discovered that way are "simple", in the sense that they only require looking
at a single instruction, and not where the arguments of that instruction came
from. They also don't require any knowledge about the properties of the
arguments of the instructions (e.g. that they are positive).

The rewrites in this post have mostly been in PyPy's JIT already. But now we
mechanically confirmed that they are correct. I've also added the remaining
useful looking ones, in particular `int_eq(x, 0) -> int_is_zero(x)` etc.

If we wanted to scale this approach up, we would have to work much harder!
There are a bunch of problems that come with generalizing the approach to
looking at sequences of instructions:

- Combinatorial explosion: if we look at sequences of instructions, we very
  quickly get a combinatorial explosion and it becomes untractable to try all
  combinations.

- Finding non-minimal patterns: Some complicated simplifications can be
  instances of simpler ones. For example, because `int_add(x, 0) -> x`, it's
  also true that `int_add(int_sub(x, y), 0) -> int_sub(x, y)`. If we simply
  generate all possible sequences, we will find the latter simplification rule,
  which we would usually not care about.

- Unclear usefulness: if we simply generate all rewrites up to a certain number
  of instructions, we will get a lot of patterns that are useless in the sense
  that they typically aren't found in realistic programs. It would be much
  better to somehow focus on the patterns that real benchmarks are using.

In the [next blog post](finding-missing-optimizations-z3.html) I'll discuss an alternative approach to simply generating
all possible sequences of instructions, that tries to address these problems.
This works by analyzing the real traces of benchmarks and mining those for
inefficiencies, which only shows problems that occur in actual programs.


## Sources

I've been re-reading a lot of blog posts from John's blog:

- [Let’s Work on an LLVM Superoptimizer](https://blog.regehr.org/archives/1109)
- [Early Superoptimizer Results](https://blog.regehr.org/archives/1146)
- [A Few Synthesizing Superoptimizer Results](https://blog.regehr.org/archives/1252)
- [Synthesizing Constants](https://blog.regehr.org/archives/1636)


but also papers:

- [A Synthesizing Superoptimizer](https://arxiv.org/pdf/1711.04422)
- [Hydra: Generalizing Peephole Optimizations with Program Synthesis](https://dl.acm.org/doi/pdf/10.1145/3649837)


Another of my favorite blogs has been [Philipp Zucker's
blog](https://www.philipzucker.com/) in the last year or two, lots of excellent
posts about/using Z3 on there.
