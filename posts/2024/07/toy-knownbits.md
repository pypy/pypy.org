<!--
.. title: A Knownbits Abstract Domain for the Toy Optimizer, Correctly
.. slug: toy-knownbits
.. date: 2024-07-30 12:00:00 UTC
.. tags: toy-optimizer, z3
.. category:
.. link:
.. description:
.. type: text
.. has_math: True
.. author: CF Bolz-Tereick
-->

After Max' introduction to abstract interpretation for the toy optimizer in the
last post, I want to present a more complicated abstract domain in this post.
This abstract domain reasons about the individual bits of a variable in a trace.
Every bit can be either "known zero", "known one" or "unknown". The abstract
domain is useful for optimizing integer operations that perform integer
manipulations.

The presentation in this post will still be in the context of the toy optimizer.
We'll spend a significant part of the post convincing ourselves that the code
that we're writing is really correct, using both property-based testing and
proofs (again with Z3).

PyPy has implemented and merged a more complicated version of the same abstract
domain for the "real" PyPy JIT. A more thorough explanation of that real world
implementation will follow.

TODO: add acknowledgements (at least Nico, Max, Santosh, Armin etc).

## Motivation

In many programs that do bit-manipulation of integers, some of the bits of the
integer variables of the program can be known. Here's a simple example:

```
x = a | 1
...
if x & 1:
    ...
else:
    ...
```

After the assignment `x = a | 1`, we know that the lowest bit of `x` must be `1`
(the other bits are unknown) and can remove the condition `x & 1` by
constant-folding it to `1`.

Another (more complicated) example is:

```
assert i & 0b111 == 0 # check that i is a multiple of 8
j = i + 16
assert j & 0b111 == 0
```

This kind of code could e.g. happen in a CPU emulator, where `i` and `j` are
integers that represent emulated pointers, and the `assert`s are alignment
checks. The first assert implies that the lowest three bits of i must be `0`.
Adding 16 to such a number produces a result where the lowest three bits are
again all `0`, therefore the second assert is always true. So we would like a
compiler to remove the second assert.

Both of these will optimizations are doable with the help of the knownbits
domain that we'll discuss in the rest of the post.


## The Knownbits Abstract Domain

An abstract value of the knownbits domain needs to be able to store for every
bit of an integer, whether it is known 0, known 1, or unknown. To represent
three different states, we need 2 bits, which we will call `one` and `unknown`.
Here's the encoding:

| one | unknown | knownbit |
|-----|---------|---------:|
| 0   | 0       |        0 |
| 1   | 0       |        1 |
| 0   | 1       |        ? |
| 1   | 1       |  illegal |

The `unknown` bit is set if we don't know the value of the bit ("?"), the `one`
bit is set if the bit is known to be a `1`.

We don't just want to encode a single bit, however. Instead, we want to do this
for all the bits of an integer variable. Therefore the instances of the abstract
domain get two integer fields `ones` and `unknowns`, where each pair of
corresponding bits encodes the knowledge about the corresponding bit of the
integer variable in the program.

We can start implementing a Python class that works like this:

```python
from dataclasses import dataclass

@dataclass(eq=False)
class KnownBits:
    ones : int
    unknowns : int

    def __post_init__(self):
        if isinstance(self.ones, int):
            assert self.is_well_formed()

    def is_well_formed(self):
        # a bit cannot be both 1 and unknown
        return self.ones & self.unknowns == 0

    @staticmethod
    def from_constant(const : int):
        """ Construct a KnownBits corresponding to a constant, where all bits
        are known."""
        return KnownBits(const, 0)

    def is_constant(self):
        """ Check if the KnownBits instance represents a constant. """
        # it's a constant if there are no unknowns
        return self.unknowns == 0


```

We can also add some convenience properties. Sometimes it is easier to work with
an integer where all the *known* bits are set, or one where all the known zeros
are set:

```python
class KnownBits:
    ...

    @property
    def knowns(self):
        """ return an integer where the known bits are set. """
        # the knowns are just the unknowns, inverted
        return ~self.unknowns

    @property
    def zeros(self):
        """ return an integer where the places that are known zeros have a bit
        set. """
        # it's a 0 if it is known, but not 1
        return self.knowns & ~self.ones
```

Also, for debugging and for writing tests we want a way to print the known bits
in a human-readable form, and also to have a way to construct a `KnownBits`
instance from a string  (it's not important to understand the details of
`__str__` or `from_str` for the rest of the post).

```python
class KnownBits:
    ...

    def __repr__(self):
        if self.is_constant():
            return f"KnownBits.from_constant({self.ones})"
        return f"KnownBits({self.ones}, {self.unknowns})"

    def __str__(self):
        res = []
        ones, unknowns = self.ones, self.unknowns
        # construct the string representation right to left
        while 1:
            if not ones and not unknowns:
                break # we leave off the leading known 0s
            if ones == -1 and not unknowns:
                # -1 has all bits set in two's complement, so the leading
                # bits are all 1
                res.append('1')
                res.append("...")
                break
            if unknowns == -1:
                # -1 has all bits set in two's complement, so the leading bits
                # are all ?
                assert not ones
                res.append("?")
                res.append("...")
                break
            if unknowns & 1:
                res.append('?')
            elif ones & 1:
                res.append('1')
            else:
                res.append('0')
            ones >>= 1
            unknowns >>= 1
        if not res:
            res.append('0')
        res.reverse()
        return "".join(res)

    @staticmethod
    def from_str(s):
        """ Construct a KnownBits instance that from a string. String can start
        with ...1 to mean that all higher bits are 1, or ...? to mean that all
        higher bits are unknown. Otherwise it is assumed that the higher bits
        are all 0. """
        ones, unknowns = 0, 0
        startindex = 0
        if s.startswith("...?"):
            unknowns = -1
            startindex = 4
        elif s.startswith("...1"):
            ones = -1
            startindex = 4
        for index in range(startindex, len(s)):
            ones <<= 1
            unknowns <<= 1
            c = s[index]
            if c == '1':
                ones |= 1
            elif c == '?':
                unknowns |= 1
        return KnownBits(ones, unknowns)
```

Let's write a unit tests for `str`:

```python
def test_str():
    assert str(KnownBits.from_constant(0)) == '0'
    assert str(KnownBits.from_constant(5)) == '101'
    assert str(KnownBits(5, 0b10)) == '1?1'
    assert str(KnownBits(~0b1111, 0b10)) == '...100?0'
    assert str(KnownBits(1, ~0b1)) == '...?1'
```

An instance of `KnownBits` represents a set of integers, namely those that match
the known bits stored in the instance. We can write a method `contains` that
takes an `int` and returns `True` if the value matches the pattern of the known
bits:


```python
class KnownBits:
    ...

    def contains(self, value : int):
        """ Check whether the KnownBits instance contains the concrete integer
        `value`. """
        # check whether value matches the bit pattern. in the places where we
        # know the bits, the value must agree with ones.
        return value & self.knowns == self.ones
```

and a test:

```python
def test_contains():
    k1 = KnownBits.from_str('1?1')
    assert k1.contains(0b111)
    assert k1.contains(0b101)
    assert not k1.contains(0b110)
    assert not k1.contains(0b011)

    k2 = KnownBits.from_str('...?1') # all odd numbers
    for i in range(-101, 100):
        assert k2.contains(i) == (i & 1)
```

## Transfer Functions

Now that we have implemented the basics of the `KnownBits` class, we need to
start implementing the transfer functions. They are for computing what we know
about the *results* of an operation, given the knownledge we have about the bits
of the arguments.

We'll start with a simple unary operation, `invert(x)` (which is `~x` in Python
and C syntax), which flips all the bits of at integer. If we know some bits of
the arguments, we can compute the corresponding bits of the result. The unknown
bits remain unknown.

Here's the code:

```python
class KnownBits:
    ...

    def abstract_invert(self):
        # self.zeros has bits set where the known 0s are in self
        return KnownBits(self.zeros, self.unknowns)

```

And a unit-test:

```python
def test_invert():
    k1 = KnownBits.from_str('01?01?01?')
    k2 = k1.abstract_invert()
    assert str(k2) == '...10?10?10?'

    k1 = KnownBits.from_str('...?')
    k2 = k1.abstract_invert()
    assert str(k2) == '...?'
```

Before we continue with further transfer functions, we'll think about
correctness of the transfer functions and build up some test infrastructure. To
test transfer functions, it's quite important to move being simple example-style
unit tests. The state-space for more complicated binary transfer functions is
extremely large and it's too easy to do something wrong in a corner case.
Therefore we'll look at property-based-test for `KnownBits` next.


## Property-based Tests with Hypothesis

We want to do property-based tests of `KnownBits`, to try
make it less likely that we'll get a corner-case in the implementation wrong.
We'll use [Hypothesis](https://hypothesis.readthedocs.io/en/latest/) for that.

I can't give a decent introduction to Hypothesis here, but want to give a few
hints about the API. Hypothesis is a way to run unit tests with randomly
generated input. It provides *strategies* to describe the data that the test
functions expects. Hypothesis provides primitive strategies (for things like
integers, strings, floats, etc) and ways to build composite strategies out of
the primitive ones.

To be able to write the tests, we need to generate random `KnownBits` instances,
and we also want an `int` instance that is a member of the `KnownBits` instance.
We generate tuples of `(KnownBits, int)` together, to ensure this property.
We'll ask Hypothesis to generate us a random concrete `int` as the concrete
value, and then we'll also generate a second random `int` to use as the
`unknown` masks (i.e. which bits of the concrete int we don't know in the
`KnownBits` instance). Here's a function that takes two such ints and builds the
tuple:

```python
def build_knownbits_and_contained_number(concrete_value : int, unknowns : int):
    # to construct a valid KnownBits instance, we need to mask off the unknown
    # bits
    ones = concrete_value & ~unknowns
    return KnownBits(ones, unknowns), concrete_value
```

We can turn this function into a hypothesis strategy to generate input data
using the `strategies.builds` function:

```python
from hypothesis import strategies, given

ints = strategies.integers()

random_knownbits_and_contained_number = strategies.builds(
    build_knownbits_and_contained_number,
    ints, ints
)
```

One important special case of `KnownBits` are the constants, which contain only
a single concrete value. We'll also generate some of those specifically, and
then combine the `random_knownbits_and_contained_number` strategy with it:

```python
constant_knownbits = strategies.builds(
    lambda value: (KnownBits.from_constant(value), value),
    ints
)

knownbits_and_contained_number = constant_knownbits | random_knownbits_and_contained_number
```


Now we can write the first property-based tests, for the `KnownBits.contains`
method:

```python
@given(knownbits_and_contained_number)
def test_contains(t):
    k, n = t
    assert k.contains(t)
```

The `@given` decorator is used to tell Hypothesis which strategy to use to
generate random data for the test function. Hypothesis will run the test with a
number of random examples (100 by default). If it finds an error, it will try to
minimize the example needed that demonstrates the problem, to try to make it
easier to understand what is going wrong. It also saves all failing cases into
an example database and tries them again on subsequent runs.

This test is as much a check for whether we got the strategies right as it is
for the logic in `KnownBits.contains`. Here's an example output of random
concrete and abstract values that we are getting here:


```
110000011001101 ...?0???1
...1011011 ...1011011
...1001101110101000010010011111011 ...1001101110101000010010011111011
...1001101110101000010010011111011 ...100110111010100001?010?1??1??11
1000001101111101001011010011111101000011000111011001011111101 1000001101111101001011010011111101000011000111011001011111101
1000001101111101001011010011111101000011000111011001011111101 1000001101111101001011010011111101000011000111????01?11?????1
1111100000010 1111100000010
1111100000010 ...?11111?00000??
110110 110110
110110 ...?00?00????11??10
110110 ??0??0
...100010111011111 ...?100?10111??111?
...1000100000110001 ...?000?00000??000?
110000001110 ...?0?0??000?00?0?0000000?00???0000?????00???000?0?00?01?000?0??1??
110000001110 ??000000???0
1011011010000001110101001111000010001001011101010010010001000000010101010010001101110101111111010101010010101100110000011110000 1011011010000001110101001111000010001001011101010010010001000000010101010010001101110101111111010101010010101100110000011110000
...1011010010010100 ...1011010010010100
...1011111110110011 ...1011111110110011
101000011110110 101000011?10?1?
100101 ?00?0?
```

That looks suitably random, but we might want to bias our random numbers a
little bit towards common error values like small constants, powers of two, etc.
Like this:

```python
INTEGER_WIDTH = 64
# some small integers
ints_special = set(range(100))
# powers of two
ints_special = ints_special.union(1 << i for i in range(INTEGER_WIDTH - 2))
# powers of two - 1
ints_special = ints_special.union((1 << i) - 1 for i in range(INTEGER_WIDTH - 2))
# negative versions of what we have so far
ints_special = ints_special.union(-x for x in ints_special)
# bit-flipped versions of what we have so far
ints_special = ints_special.union(~x for x in ints_special)
ints_special = list(ints_special)
# sort them (because hypothesis simplifies towards earlier elements in the list)
ints_special.sort(key=lambda element: (abs(element), element < 0))

ints = strategies.sampled_from(ints_special) | strategies.integers()
```

Now we get data like this:

```
1110 1110
...10000000000000000001 ...10000??0??0000??00?1
1 ??0??0000??00?1
1 ?
...10101100 ...10101100
110000000011001010111011111111111111011110010001001100110001011 ...?0?101?
110000000011001010111011111111111111011110010001001100110001011 ??00000000??00?0?0???0??????????????0????00?000?00??00??000?0??
...1011111111111111111111111111 ...?11?11??
...1011111111111111111111111111 ...?0??????????????????????????
0 ...?0??????????????????????????
101101 101101
111111111111111111111111111111111111111111111 111111111111111111111111111111111111111111111
10111 10111
...101100 ...1?111011?0
101000 ?001010?0
101000 ?0?000
110010 110010
...100111 ...100111
1111011010010 1111011010010
...1000000000000000000000000000000000000 ...1000000000000000000000000000000000000
```

We can also write a test that checks that the somewhat tricky logic in
`__str__` and `from_str` is correct, by making sure that the two functions
round-trip (ie converting a `KnownBits` to a string and then back to a
`KnownBits` instance yields the abstract value).

```python
@given(knownbits_and_contained_number)
def test_hypothesis_str_roundtrips(t1):
    k1, n1 = t1
    s = str(k1)
    k2 = KnownBits.from_str(s)
    assert k1.ones == k2.ones
    assert k1.unknowns == k2.unknowns
```

Now let's actually apply this infrastructure to test `abstract_invert`.


## When are Transfer Functions Correct? How do we test them?

Abstract value, i.e. instances of `KnownBits` represent *sets* of concrete
values. We want the transfer functions to compute *overapproximations* of the
concrete values. So if we have an arbitrary abstract value `k`, with a concrete
number `n` that is a member of the abstract values (i.e.
`k.contains(n) == True`) then the result of the concrete operation `op(n)`
**must** be a member of the result of the abstract operation `k.abstract_op()`
(i.e. `k.abstract_op().contains(op(n)) == True`).

Checking the correctness/overapproximation property is a good match for
hypothesis. Here's what the test for `abstract_invert` looks like:

```python
@given(knownbits_and_contained_number)
def test_hypothesis_invert(t):
    k1, n1 = t1
    n2 = ~n1 # compute the real result
    k2 = k1.abstract_invert() # compute the abstract result
    assert k2.contains(n2) # the abstract result must contain the real result
```

This is the *only* condition needed for `abstract_invert` to be correct. If
`abstract_invert` fulfils this property for every combination of abstract and
concrete value then `abstract_invert` is *correct*. Note however, that this test
does not actually check whether `abstract_invert` gives us precise results. A
correct (but imprecise) implementation of `abstract_invert` would simply return
a completely unknown result, regardless of what is known about the input
`KnownBits`.

## Implementing Binary Transfer Functions

Now we have infrastructure in place for testing transfer functions with random
inputs. With that we can start thinking about the more complicated case, that of
binary operations. Let's start with the simpler ones, `and` and `or`. For `and`,
we can know a `0` bit in the result if either of the input bits are known `0`;
or we can know a `1` bit in the result if both input bits are known `1`.
Otherwise the resulting bit is unknown. Let's look at all the combinations:

```
and
input1: 000111???
input2: 01?01?01? 
result: 00001?0??
```

```python
class KnownBits:
    ...

    def abstract_and(self, other):
        ones = self.ones & other.ones # known ones
        knowns = self.zeros | other.zeros | ones
        return KnownBits(ones, ~knowns)
```

Here's an example unit-test and a property-based test for `and`:

```python
def test_and():
    # test all combinations of 0, 1, ? in one example
    k1 = KnownBits.from_str('01?01?01?')
    k2 = KnownBits.from_str('000111???')
    res = k1.abstract_and(k2)     # should be: 0...00001?0??
    assert str(res) ==   "1?0??"

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_and(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    assert k3.contains(n3)
```

To implement `or` is pretty similar. The result is known `1` where either of the
inputs is `1`. The result is known `0` where both inputs are known `0`, and `?`
otherwise.

```
or
input1: 000111???
input2: 01?01?01? 
result: 01?111?1?
```

```python
class KnownBits:
    ...

    def abstract_or(self, other):
        ones = self.ones | other.ones
        zeros = self.zeros & other.zeros
        knowns = ones | zeros
        return KnownBits(ones, ~knowns)
```

Here's an example unit-test and a property-based test for `or`:

```python
def test_or():
    k1 = KnownBits.from_str('01?01?01?')
    k2 = KnownBits.from_str('000111???')
    res = k1.abstract_or(k2)     # should be:  0...01?111?1?
    assert str(res) ==   "1?111?1?"

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_or(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_or(k2)
    n3 = n1 | n2
    assert k3.contains(n3)
```

Implementing support for `abstract_xor` is relatively simple, and left as an
exercise :-).

## Addition and Subtraction

`invert`, `and`, and `or` are relatively simple transfer functions to write,
because they compose over the individual bits of the integers. The arithmetic
functions `add` and `sub` are significantly harder, because of carries and
borrows. Coming up with the formulas for them and gaining an intuitive
understanding is quite tricky and involves carefully going through a few
examples with pen and paper. We didn't come up with the implementation
ourselves, but instead took them from the TODO paper. Here's the code, with
example tests and hypothesis tests:

```python
class KnownBits:
    ...

    def abstract_add(self, other):
        sum_ones = self.ones + other.ones
        sum_unknowns = self.unknowns + other.unknowns
        all_carries = sum_ones + sum_unknowns
        ones_carries = all_carries ^ sum_ones
        unknowns = self.unknowns | other.unknowns | ones_carries
        ones = sum_ones & ~unknowns
        return KnownBits(ones, unknowns)

    def abstract_sub(self, other):
        diff_ones = self.ones - other.ones
        val_borrows = (diff_ones + self.unknowns) ^ (diff_ones - other.unknowns)
        unknowns = self.unknowns | other.unknowns | val_borrows
        ones = diff_ones & ~unknowns
        return KnownBits(ones, unknowns)


def test_add():
    k1 = KnownBits.from_str('0?10?10?10')
    k2 = KnownBits.from_str('0???111000')
    res = k1.abstract_add(k2)
    assert str(res) ==   "?????01?10"

def test_sub():
    k1 = KnownBits.from_str('0?10?10?10')
    k2 = KnownBits.from_str('0???111000')
    res = k1.abstract_sub(k2)
    assert str(res) ==   "...?11?10"
    k1 = KnownBits.from_str(    '...1?10?10?10')
    k2 = KnownBits.from_str('...10000???111000')
    res = k1.abstract_sub(k2)
    assert str(res) ==   "111?????11?10"

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_add(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_add(k2)
    n3 = n1 + n2
    assert k3.contains(n3)

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_sub(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_sub(k2)
    n3 = n1 - n2
    assert k3.contains(n3)
```

Now we are in a pretty good situation, and have implemented abstract versions
for a bunch of important arithmetic and binary functions. What's also surprising
is that the implementation of all of the transfer functions is quite efficient.
We didn't have to write loops over the individual bits at all, instead we found
closed form expressions using primitive operations on the underlying integers
`ones` and `unknowns`. This means that computing the results of abstract
operations is quite efficient, which is important when using the abstract domain
in the context of a JIT compiler.

## Proving correctness of the transfer functions with Z3

As one can probably tell from my most recent posts, I've been thinking about
compiler correctness a lot recently. Getting the transfer functions absolutely
correct is really crucial, because a bug in them would lead to miscompilation of
Python code when the abstract domain is added to the JIT. While the randomized
tests are great, it's still entirely possible for them to miss bugs. The state
space for the arguments of a binary transfer function is `3**64 * 3**64`, and if
only a small part of that contains wrong behaviour it would be really unlikely
for us to find it with random tests by chance. Therefore I was reluctant to
merge the PyPy branch that contained the new abstract domain for a long time.

To increase our confidence in the correctness of the transfer functions further,
we can use Z3 to *prove* their correctness, which gives us much stronger
guarantees (not 100%, obviously). In this subsection I will show how to do that.

The condition that we prove for 

Here's an attempt to do this manually in the Python repl:

```
>>>> import z3
>>>> solver = z3.Solver()
>>>> # like last blog post, proof by failing to find counterexamples
>>>> def prove(cond): assert solver.check(z3.Not(cond)) == z3.unsat
>>>>
>>>> # let's set up a z3 bitvector variable for an abitrary concrete value
>>>> n1 = z3.BitVec('concrete_value', 64)
>>>> n1
concrete_value
>>>> # due to operator overloading we can manipulate z3 formulas
>>>> n2 = ~n1
>>>> n2
~concrete_value
>>>> 
>>>> # now z3 bitvector variables for the ones and zeros fields
>>>> ones = z3.BitVec('abstract_ones', 64)
>>>> unknowns = z3.BitVec('abstract_unknowns', 64)
>>>> # we construct a KnownBits instance with the z3 variables
>>>> k1 = KnownBits(ones, unknowns)
>>>> # due to operator overloading we can call the methods on k1:
>>>> k2 = k1.abstract_invert()
>>>> k2.ones
~abstract_unknowns & ~abstract_ones
>>>> k2.unknowns
abstract_unknowns
>>>> # here's the correctness condition that we want to prove:
>>>> k2.contains(n2)
~concrete_value & ~abstract_unknowns ==
~abstract_unknowns & ~abstract_ones
>>>> # let's try
>>>> prove(k2.contains(n2))
Traceback (most recent call last):
  File "/home/cfbolz/bin/pypy-c-jit-184949-5ab4e2e078e2-linux64/lib/pypy3.10/code.py", line 90, in runcode
    exec(code, self.locals)
  File "<stdin>", line 1, in <module>
  File "<stdin>", line 1, in prove
AssertionError
>>>> # it doesn't work! let's look at the countexample to see why:
>>>> solver.model()
[abstract_unknowns = 0,
 abstract_ones = 0,
 concrete_value = 1]
>>>> # we can build a KnownBits instance with the values in the
>>>> # counterexample:
>>>> ~1 # concrete result
-2
>>>> counter_example_k1 = KnownBits(0, 0)
>>>> counter_example_k1
KnownBits.from_constant(0)
>>>> counter_example_k2 = counter_example_k1.abstract_invert()
>>>> counter_example_k2
KnownBits.from_constant(-1)
>>>> # let's check the failing condition
>>>> counter_example_k2.contains(~1)
False
```

What is the problem here? We didn't tell Z3 that `n1` was supposed to be a
member of `k1`. We can add this as a precondition to the solver, and then the
prove works:

```
>>>> solver.add(k1.contains(n1))
>>>> prove(k2.contains(n2)) # works!
```

This is super cool! It's really a proof about the actual implementation, because
we call the implementation methods directly, and due to the operator overloading
that Z3 does we can be sure that we are actually checking a statement that
corresponds to the Python code. This eliminates one source of errors in formal
methods.

Doing the proof manually on the Python REPL is kind of annoying though, and we
also would like to make sure that the proofs are re-done when we change the
code. What we would really like to do is writing the proofs as a unit-test that
we can run in CI. Doing this is possible, and the unit tests that really perform
proofs look pleasingly similar to the Hypothesis-based ones.

First we need to set up a bit of infrastructure:

```python
INTEGER_WIDTH = 64

def BitVec(name):
    return z3.BitVec(name, INTEGER_WIDTH)

def BitVecVal(val):
    return z3.BitVecVal(val, INTEGER_WIDTH)

solver = z3.Solver()

n1 = BitVec("n1")
k1 = KnownBits(BitVec("n1_ones"), BitVec("n1_unkowns"))
solver.add(k1.contains(n1))

n2 = BitVec("n2")
k2 = KnownBits(BitVec("n2_ones"), BitVec("n2_unkowns"))
solver.add(k2.contains(n2))

def prove(cond):
    z3res = solver.check(z3.Not(cond))
    if z3res != z3.unsat:
        assert z3res == z3.sat # can't be timeout, we set no timeout
        # make the counterexample global, to make inspecting the bug in pdb
        # easier
        global model 
        model = solver.model()
        # print the count-example values for n1, n2, k1, k2:
        print(f"n1={model.eval(n1)}, n2={model.eval(n2)}")
        counter_example_k1 = KnownBits(model.eval(k1.ones).as_signed_long(),
                                       model.eval(k1.unknowns).as_signed_long())
        counter_example_k2 = KnownBits(model.eval(k2.ones).as_signed_long(),
                                       model.eval(k2.unknowns).as_signed_long())
        print(f"k1={counter_example_k1}, k2={counter_example_k2}")
        print(f"but {cond=} evaluates to {model.eval(cond)}")
        raise ValueError(solver.model())
```

And then we can write proof-unit-tests like this:


```python
def test_z3_abstract_invert():
    k2 = k1.abstract_invert()
    n2 = ~n1
    prove(k2.contains(n2))

def test_z3_abstract_and():
    k3 = k1.abstract_and(k2)
    n3 = n1 & n2
    prove(k3.contains(n3))

def test_z3_abstract_or():
    k3 = k1.abstract_or(k2)
    n3 = n1 | n2
    prove(k3.contains(n3))

def test_z3_abstract_add():
    k3 = k1.abstract_add(k2)
    n3 = n1 + n2
    prove(k3.contains(n3))

def test_z3_abstract_sub():
    k3 = k1.abstract_sub(k2)
    n3 = n1 - n2
    prove(k3.contains(n3))
```

(it's possible to write a bit more Python-metaprogramming-magic and unify the
Hypothesis and Z3 tests into the same test definition, and then first try to
find some random counterexamples and if that works, do a Z3 proof.)


## Cases where this style of Z3 proof doesn't work

Unfortunately the approach described in the previous section only works for a
very small number of cases. It breaks down as soon as the `KnownBits` methods
that we're calling contain any `if` conditions (including hidden ones like
the short-circuiting `and` and `or` in Python). Let's look at an example and
implement `abstract_eq`. `eq` is supposed to be an operation that compares two
integers and returns 0 or 1 if they are different or equal, respectively.
Implementing this in knownbits looks like this with example and hypothesis
tests:

```python
class KnownBits:
    ...

    def abstract_eq(self, other):
        # the result is a 0, 1, or ?

        # can only be known equal if they are both constants
        if self.is_constant() and other.is_constant() and self.ones == other.ones:
            return KnownBits.from_constant(1)
        # check whether we have known disagreeing bits, then we know the result
        # is 0
        if self._disagrees(other):
            return KnownBits.from_constant(0)
        return KnownBits(0, 1) # an unknown boolean

    def _disagrees(self, other):
        # check whether the bits disagree in any place where both are known
        both_known = self.knowns & other.knowns
        return self.ones & both_known != other.ones & both_known

def test_eq():
    k1 = KnownBits.from_str('...?')
    k2 = KnownBits.from_str('...?')
    assert str(k1.abstract_eq(k2)) == '?'
    k1 = KnownBits.from_constant(10)
    assert str(k1.abstract_eq(k1)) == '1'
    k1 = KnownBits.from_constant(10)
    k2 = KnownBits.from_constant(20)
    assert str(k1.abstract_eq(k2)) == '0'

@given(knownbits_and_contained_number, knownbits_and_contained_number)
def test_hypothesis_eq(t1, t2):
    k1, n1 = t1
    k2, n2 = t2
    k3 = k1.abstract_eq(k2)
    assert k3.contains(int(n1 == n2))
```

Trying to do the proof in the same style as before breaks:

```python
>>>> k3 = k1.abstract_eq(k2)
Traceback (most recent call last):
  File "<stdin>", line 1, in <module>
  File "knownbits.py", line 246, in abstract_eq
    if self._disagrees(other):
  File "venv/site-packages/z3/z3.py", line 381, in __bool__
    raise Z3Exception("Symbolic expressions cannot be cast to concrete Boolean values.")
z3.z3types.Z3Exception: Symbolic expressions cannot be cast to concrete Boolean values.
```

We cannot call `abstract_eq` on a `KnownBits` with Z3 variables as fields,
because once we hit an `if` statement, the whole approach of relying on the
operator overloading breaks down. Z3 doesn't actually parse the Python code or
anything advanced like that, we rather build an expression only by running the
code and letting the Z3 formulas build up.

To still prove the correctness of `abstract_eq` we need to manually transform
the control flow logic of the function into a Z3 formula that uses the `z3.If`
expression, using a small helper function:

```python
def z3_cond(b, trueval=1, falseval=0):
    return z3.If(b, BitVecVal(trueval), BitVecVal(falseval))

def test_z3_abstract_eq_logic():
    n3 = z3_cond(n1 == n2) # concrete result
    # follow the *logic* of abstract_eq, we can't call it due to the ifs in it
    case1cond = z3.And(k1.is_constant(), k2.is_constant(), k1.ones == k2.ones)
    case2cond = k1._disagrees(k2)

    # ones is 1 in the first case, 0 otherwise
    ones = z3_cond(case1cond, 1, 0)

    # in the first two cases, unknowns is 0, 1 otherwise
    unknowns = z3_cond(z3.Or(case1cond, case2cond), 0, 1)
    k3 = KnownBits(ones, unknowns)
    prove(k3.contains(n3))
```

This proof works. It is a lot less satisfying than the previous ones though,
because we could have done an error in the manual transcription from Python code
to Z3 formulas (there are possibly more heavy-handed approaches where we do
this transformation more automatically using e.g. the `ast` module to analyze
the source code, but that's a much more complicated researchy project). To
lessen this problem somewhat we can factor out the parts of the logic that don't
have any conditions into small helper methods (like `_disagrees` in this
example) and use them in the manual conversion of the code to Z3 formulas.

The final condition that Z3 checks, btw, is this one:

```
If(n1 == n2, 1, 0) &
~If(Or(And(n1_unkowns == 0,
           n2_unkowns == 0,
           n1_ones == n2_ones),
       n1_ones & ~n1_unkowns & ~n2_unkowns !=
       n2_ones & ~n1_unkowns & ~n2_unkowns),
    0, 1) ==
If(And(n1_unkowns == 0, n2_unkowns == 0, n1_ones == n2_ones),
   1, 0)
```

## Making Statements about Precision

## Using the Abstract Domain in the Toy Optimizer
