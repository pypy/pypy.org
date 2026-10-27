.. title: The Shift of Theseus — Toy Bit Provenance Abstract Domain
.. slug: toy-bit-provenance
.. date: 2026-10-27 8:04:49 UTC+02:00
.. tags: toy-optimizer, performance
.. category:
.. link:
.. description:
.. type: rest
.. author: CF Bolz-Tereick

The `Knownbits Toy abstract domain`_ that I wrote about earlier is great for
all kinds of bit manipulation rewrites. However, it is not particularly good at
recognizing where bits move around in a sequence of instructions. It has a
notion of "this bit is ``0`` or ``1`` or unknown" but no notion of "this bit is the
same as this other bit". This prevents it from optimizing something like this:

.. code::

    x = ...
    a = x & 0x0f
    b = x << 60
    c = b >> 60
    result = a & c

Here ``a`` and ``c`` compute the same value, so it can be optimized to ``result = a``.
It is possible to do this optimization with local `peephole rewrite rules`_ too,
but doing that requires adding a lot of these rules, and if one is missing we
might miss collapsing a long sequence of operations.

In this post I want to talk about a more complicated `abstract domain`_ that is
great at optimizing this kind of bit movement. It's a "bit provenance" domain.
For every SSA_ variable in a trace, it computes where each bit from the variable
comes from (or whether it's constant ``0`` or ``1``). In particular it can
track if a bit in one variable must be the same as the bit of another variable
at another position.

For the example above, the domain would store the following provenance
information. Nothing is known about ``x``, so its bits refer to themselves.
Using 64-bit integers and a logical right shift, we get this table (most
significant bits first):


.. class:: table table-bordered table-sm

+---------------------+--------+--------+--------+--------+--------+-----+-------+-------+-------+-------+-------+
| operation           | Bit 63 | Bit 62 | Bit 61 | Bit 60 | Bit 59 | ... | Bit 4 | Bit 3 | Bit 2 | Bit 1 | Bit 0 |
+=====================+========+========+========+========+========+=====+=======+=======+=======+=======+=======+
| ``x = ...``         |  x[63] |  x[62] |  x[61] |  x[60] |  x[59] | ... |  x[4] |  x[3] |  x[2] |  x[1] |  x[0] |
+---------------------+--------+--------+--------+--------+--------+-----+-------+-------+-------+-------+-------+
| ``a = x & 0x0f``    |      0 |      0 |      0 |      0 |      0 | ... |     0 |  x[3] |  x[2] |  x[1] |  x[0] |
+---------------------+--------+--------+--------+--------+--------+-----+-------+-------+-------+-------+-------+
| ``b = x << 60``     |   x[3] |   x[2] |   x[1] |   x[0] |      0 | ... |     0 |     0 |     0 |     0 |     0 |
+---------------------+--------+--------+--------+--------+--------+-----+-------+-------+-------+-------+-------+
| ``c = b >> 60``     |      0 |      0 |      0 |      0 |      0 | ... |     0 |  x[3] |  x[2] |  x[1] |  x[0] |
+---------------------+--------+--------+--------+--------+--------+-----+-------+-------+-------+-------+-------+
| ``result = a & c``  |      0 |      0 |      0 |      0 |      0 | ... |     0 |  x[3] |  x[2] |  x[1] |  x[0] |
+---------------------+--------+--------+--------+--------+--------+-----+-------+-------+-------+-------+-------+

Then we can directly conclude that ``result`` is the same value as ``a``.

In the rest of the post I'll describe how the domain values store this
information, how the transfer functions work and how we can use the abstract
domain to optimize.

.. contents:: Contents
   :depth: 2
   :backlinks: none

Implementing the Domain
------------------------

We'll start with reusing the `toy optimizer`_ from the `previous posts`_, in the fold for completeness’ sake.

.. raw:: html

   <details>
   <summary>toy infrastructure</summary>



.. code:: python

    from dataclasses import dataclass

    INTEGER_WIDTH = 64
    INT_MASK = 2 ** INTEGER_WIDTH - 1

    class Value:
        def find(self):
            raise NotImplementedError("abstract")


    @dataclass(eq=False)
    class Operation(Value):
        name : str
        args : list[Value]

        forwarded : Value | None = None

        def find(self) -> Value:
            op = self
            while isinstance(op, Operation):
                next = op.forwarded
                if next is None:
                    return op
                op = next
            return op

        def arg(self, index):
            return self.args[index].find()

        def make_equal_to(self, value : Value):
            self.find().forwarded = value


    @dataclass(eq=False)
    class Constant(Value):
        value : object

        def find(self):
            return self


    class Block(list):
        def __getattr__(self, opname):
            def wraparg(arg):
                if not isinstance(arg, Value):
                    arg = Constant(arg)
                return arg
            def make_op(*args):
                op = Operation(opname,
                    [wraparg(arg) for arg in args])
                self.append(op)
                return op
            return make_op


    def bb_to_str(l : Block, varprefix : str = "var"):
        def arg_to_str(arg : Value):
            if isinstance(arg, Constant):
                return str(arg.value)
            else:
                return varnames[arg]

        varnames = {}
        res = []
        for index, op in enumerate(l):
            # give the operation a name used while
            # printing:
            var =  f"{varprefix}{index}"
            varnames[op] = var
            arguments = ", ".join(
                arg_to_str(op.arg(i))
                    for i in range(len(op.args))
            )
            strop = f"{var} = {op.name}({arguments})"
            res.append(strop)
        return "\n".join(res)

    def dce(bb: Block) -> Block:
        pure = {"getarg", "int_and", "int_or", "int_xor", "int_invert",
                "int_lshift", "int_rshift"}
        used = set()
        kept = []
        for op in reversed(bb):
            if op not in used and op.name in pure:
                continue
            kept.append(op)
            for i in range(len(op.args)):
                arg = op.arg(i)
                if isinstance(arg, Operation):
                    used.add(arg)
        return Block(reversed(kept))


    def test_dce():
        bb = Block()
        x = bb.getarg(0)
        live = bb.int_or(x, 1)
        dead = bb.int_xor(live, 7)
        bb.int_and(dead, 15)
        forwarded = bb.int_and(x, 0)
        forwarded.make_equal_to(Constant(0))
        bb.dummy(live)
        bb.dummy(forwarded)

        assert bb_to_str(dce(bb), "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = int_or(optvar0, 1)
    optvar2 = dummy(optvar1)
    optvar3 = dummy(0)"""

.. raw:: html

   </details>

(The ``dce`` function was adapted from the `Prospero blog post`_.)

Then we can start implementing the domain values like this:


.. code:: python

    @dataclass(frozen=True)
    class SourceBit:
        source: Operation
        index: int
        inverted: bool = False


    @dataclass(frozen=True)
    class BitProvenance:
        # least significant bit first
        bits: tuple[int | SourceBit, ...]

        @staticmethod
        def make(bits):
            bits = tuple(bits)
            if len(bits) < INTEGER_WIDTH:
                # zero-extend, mainly for tests
                bits = bits + (0, ) * (INTEGER_WIDTH - len(bits))
            assert len(bits) == INTEGER_WIDTH
            return BitProvenance(bits)

        @staticmethod
        def from_constant(value):
            return BitProvenance(tuple((value >> i) & 1 for i in range(INTEGER_WIDTH)))

        @staticmethod
        def from_source(source: Operation):
            # nothing is known about this SSA value
            return BitProvenance(tuple(SourceBit(source, i) for i in range(INTEGER_WIDTH)))

        def get_constant(self) -> int | None:
            res = 0
            shift = 0
            for bit in self.bits:
                if isinstance(bit, SourceBit):
                    return None
                res |= bit << shift
                shift += 1
            return res


Every ``SourceBit`` refers to a bit of an SSA ``Operation``. For an SSA value that we
know nothing about, we use the ``from_source`` factory method, which returns
something of the form:

.. code:: python

    x = ... # x[63] x[62] x[61] x[60] x[59] ... x[ 3] x[ 2] x[ 1] x[0]

For a constant, the ``from_constant`` factory returns an abstract value where all
the bits are concretely known values. Constants are simply ``0`` or ``1`` and need no
source at all.

The ``inverted`` field of a ``SourceBit`` specifies whether the bit is a direct
copy of the source bit, or whether the bit is flipped.


Let's make sure we got the bit twiddling in ``from_constant`` and ``get_constant`` right by writing a Hypothesis_ test:

.. code:: python

    from hypothesis import given, strategies

    ints = strategies.integers(0, 2**64-1)

    @given(ints)
    def test_hypothesis_from_constant_get_constant_roundtrip(val):
        assert BitProvenance.from_constant(val).get_constant() == val


Implementing Transfer Functions
---------------------------------

The simplest transfer function to implement for this domain is for ``~``, bit
invert. It inverts constant bits and flips the ``inverted`` field of any
``SourceBit``. Here's a test:


.. code:: python

    def test_abstract_invert():
        source = Operation("getarg", [Constant(0)])
        x = BitProvenance.make([1, 0, SourceBit(source, 1, True), SourceBit(source, 0)])
        res = x.abstract_invert()
        assert res == BitProvenance.make((0, 1, SourceBit(source, 1), SourceBit(source, 0, True)) + (1, ) * 60)


The implementation looks like this (the reason for the ``result`` argument will become clear a bit further down):

.. code:: python

    def invert_bit(bit):
        if isinstance(bit, int):
            return bit ^ 1
        return SourceBit(bit.source, bit.index, not bit.inverted)


    class BitProvenance:
        ...

        def abstract_invert(self, result=None):
            return BitProvenance.make(tuple(invert_bit(bit) for bit in self.bits))


The shift implementations are also quite simple as long as the shift amounts
are constant, they just move bits around. If the shifts aren't constant, we
just know nothing about the result.

If we "know nothing", we want to use ``BitProvenance.from_source`` for the shift
operation. Therefore the transfer functions need to get the shift ``Operation`` as
an extra argument.


.. code:: python

    def test_lshift():
        source = Operation("getarg", [Constant(0)])
        x = BitProvenance.from_source(source) # no info

        # x << 7, the seven high bits get cut off
        seven = BitProvenance.from_constant(7)
        result = Operation("int_lshift", [source, Constant(7)])
        assert x.abstract_lshift(seven, result).bits == (0, ) * 7 + x.bits[:-7]

        # x << 65, constant 0
        big = BitProvenance.from_constant(65)
        result = Operation("int_lshift", [source, Constant(65)])
        assert x.abstract_lshift(big, result).get_constant() == 0

        # x << y, we know nothing
        amount = Operation("getarg", [Constant(1)])
        result = Operation("int_lshift", [source, amount])
        assert x.abstract_lshift(BitProvenance.from_source(amount), result) == BitProvenance.from_source(result)


    @given(ints, strategies.integers(0, 100))
    def test_hypothesis_lshift_on_constants(val, shift):
        absval = BitProvenance.from_constant(val)
        absshift = BitProvenance.from_constant(shift)
        result = Operation("int_lshift", [Constant(val), Constant(shift)])
        assert absval.abstract_lshift(absshift, result).get_constant() == (val << shift) & INT_MASK


    class BitProvenance:
        ...

        def abstract_lshift(self, other, result: Operation):
            const = other.get_constant()
            if const is None:
                return BitProvenance.from_source(result)
            if const >= INTEGER_WIDTH:
                # make oversized shift amounts return 0 for simplicity
                return BitProvenance.from_constant(0)
            if const == 0:
                return self
            return BitProvenance.make((0, ) * const + self.bits[:-const])


Logical right shift is pretty similar, except we append the zeros at the other end:


.. code:: python

    def test_rshift():
        source = Operation("getarg", [Constant(0)])
        x = BitProvenance.from_source(source) # no info

        # x >> 7, the seven low bits get cut off
        seven = BitProvenance.from_constant(7)
        result = Operation("int_rshift", [source, Constant(7)])
        assert x.abstract_rshift(seven, result).bits == x.bits[7:] + (0, ) * 7

        # x >> 65, constant 0
        big = BitProvenance.from_constant(65)
        result = Operation("int_rshift", [source, Constant(65)])
        assert x.abstract_rshift(big, result).get_constant() == 0

        # x >> y, we know nothing
        amount = Operation("getarg", [Constant(1)])
        result = Operation("int_rshift", [source, amount])
        assert x.abstract_rshift(BitProvenance.from_source(amount), result) == BitProvenance.from_source(result)


    @given(ints, strategies.integers(0, 100))
    def test_hypothesis_rshift_on_constants(val, shift):
        absval = BitProvenance.from_constant(val)
        absshift = BitProvenance.from_constant(shift)
        result = Operation("int_rshift", [Constant(val), Constant(shift)])
        assert absval.abstract_rshift(absshift, result).get_constant() == val >> shift


    class BitProvenance:
        ...

        def abstract_rshift(self, other, result: Operation):
            const = other.get_constant()
            if const is None:
                return BitProvenance.from_source(result)
            if const >= INTEGER_WIDTH:
                return BitProvenance.from_constant(0)
            if const == 0:
                return self
            return BitProvenance.make(self.bits[const:] + (0, ) * const)


Implementing Bitwise Binary Transfer Functions
-----------------------------------------------

Next are the abstract binary transfer functions ``and``, ``or``, ``xor``.
We can think about the behaviour on individual bits first. A few cases are
simple (e.g. ``a & 0 == 0``) but some need reasoning about sources.

.. code:: python

    def and_bits(a, b):
        # None means the result cannot be represented as a constant or source
        # bit
        if a == 0:
            return 0
        if b == 0:
            return 0
        if a == 1:
            return b
        if b == 1:
            return a
        assert isinstance(a, SourceBit)
        assert isinstance(b, SourceBit)
        if a == b:
            # a & a == a
            return a
        if a == invert_bit(b):
            # a & not a == 0
            return 0
        return None


    def test_and_bits():
        x = Operation("getarg", [Constant(0)])
        y = Operation("getarg", [Constant(1)])
        a = SourceBit(x, 3)
        assert and_bits(a, 0) == and_bits(0, a) == 0
        assert and_bits(a, 1) == and_bits(1, a) == a
        assert and_bits(a, a) == a
        assert and_bits(a, invert_bit(a)) == 0

        # positions disagree
        assert and_bits(a, SourceBit(x, 4)) is None

        # sources disagree
        assert and_bits(a, SourceBit(y, 3)) is None
        assert and_bits(a, SourceBit(y, 3, True)) is None

When ``and_bits`` returns ``None`` for output bit ``i``, we can use
``SourceBit(result, i)``: we don't know how that bit relates to the inputs.
The other output bits keep their own provenance, even if they refer to
different operations.

Now we can combine ``and_bits`` calls for all the bits of a ``BitProvenance``.


.. code:: python

    def test_and():
        x = Operation("getarg", [Constant(0)])
        y = Operation("getarg", [Constant(1)])
        absx = BitProvenance.from_source(x)
        absy = BitProvenance.from_source(y)

        # x & 0 == 0
        result = Operation("int_and", [x, Constant(0)])
        assert absx.abstract_and(BitProvenance.from_constant(0), result).get_constant() == 0

        # x & -1 == x
        result = Operation("int_and", [x, Constant(INT_MASK)])
        assert absx.abstract_and(BitProvenance.from_constant(INT_MASK), result) == absx

        # x & x == x
        result = Operation("int_and", [x, x])
        assert absx.abstract_and(absx, result) == absx

        # x & y: we can't usefully represent provenance, so we get fresh bits
        result = Operation("int_and", [x, y])
        assert absx.abstract_and(absy, result) == BitProvenance.from_source(result)

        # x & ~x == 0
        result = Operation("int_and", [x, Operation("int_invert", [x])])
        assert absx.abstract_and(absx.abstract_invert(), result).get_constant() == 0


    @given(ints, ints)
    def test_hypothesis_and_on_constants(a, b):
        abs_a = BitProvenance.from_constant(a)
        abs_b = BitProvenance.from_constant(b)
        result = Operation("int_and", [Constant(a), Constant(b)])
        assert abs_a.abstract_and(abs_b, result).get_constant() == a & b


    class BitProvenance:
        ...

        def abstract_and(self, other, result: Operation):
            bits = []
            for i, (bit_a, bit_b) in enumerate(zip(self.bits, other.bits)):
                bit_res = and_bits(bit_a, bit_b)
                if bit_res is None:
                    # not representable, use fresh provenance
                    bit_res = SourceBit(result, i)
                bits.append(bit_res)
            return BitProvenance.make(bits)


``or`` is very similar:

.. code:: python

    def or_bits(a, b):
        if a == 1:
            return 1
        if b == 1:
            return 1
        if a == 0:
            return b
        if b == 0:
            return a
        assert isinstance(a, SourceBit)
        assert isinstance(b, SourceBit)
        if a == b:
            # a | a == a
            return a
        if a == invert_bit(b):
            # a | not a == 1
            return 1
        return None

    def test_or_bits():
        x = Operation("getarg", [Constant(0)])
        y = Operation("getarg", [Constant(1)])
        a = SourceBit(x, 3)
        assert or_bits(a, 1) == or_bits(1, a) == 1
        assert or_bits(a, 0) == or_bits(0, a) == a
        assert or_bits(a, a) == a
        assert or_bits(a, invert_bit(a)) == 1

        # positions disagree
        assert or_bits(a, SourceBit(x, 4)) is None

        # sources disagree
        assert or_bits(a, SourceBit(y, 3)) is None
        assert or_bits(a, SourceBit(y, 3, True)) is None


    def test_or():
        x = Operation("getarg", [Constant(0)])
        y = Operation("getarg", [Constant(1)])
        absx = BitProvenance.from_source(x)
        absy = BitProvenance.from_source(y)

        # x | 0 == x
        result = Operation("int_or", [x, Constant(0)])
        assert absx.abstract_or(BitProvenance.from_constant(0), result) == absx

        # x | -1 == -1
        result = Operation("int_or", [x, Constant(INT_MASK)])
        assert absx.abstract_or(BitProvenance.from_constant(INT_MASK), result).get_constant() == INT_MASK

        # x | x == x
        result = Operation("int_or", [x, x])
        assert absx.abstract_or(absx, result) == absx

        # x | y: we can't usefully represent provenance, so we get fresh bits
        result = Operation("int_or", [x, y])
        assert absx.abstract_or(absy, result) == BitProvenance.from_source(result)

        # x | ~x == -1
        result = Operation("int_or", [x, Operation("int_invert", [x])])
        assert absx.abstract_or(absx.abstract_invert(), result).get_constant() == INT_MASK


    @given(ints, ints)
    def test_hypothesis_or_on_constants(a, b):
        abs_a = BitProvenance.from_constant(a)
        abs_b = BitProvenance.from_constant(b)
        result = Operation("int_or", [Constant(a), Constant(b)])
        assert abs_a.abstract_or(abs_b, result).get_constant() == a | b


    class BitProvenance:
        ...

        def abstract_or(self, other, result: Operation):
            bits = []
            for i, (bit_a, bit_b) in enumerate(zip(self.bits, other.bits)):
                bit_res = or_bits(bit_a, bit_b)
                if bit_res is None:
                    # not representable, use fresh provenance
                    bit_res = SourceBit(result, i)
                bits.append(bit_res)
            return BitProvenance.make(bits)

And finally here is ``xor``:


.. code:: python

    def xor_bits(a, b):
        if a == 1:
            # x ^ 1 == ~x
            return invert_bit(b)
        if b == 1:
            return invert_bit(a)
        if a == 0:
            # x ^ 0 == x
            return b
        if b == 0:
            return a
        assert isinstance(a, SourceBit)
        assert isinstance(b, SourceBit)
        if a == b:
            # a ^ a == 0
            return 0
        if a == invert_bit(b):
            # a ^ not a == 1
            return 1
        return None

    def test_xor_bits():
        x = Operation("getarg", [Constant(0)])
        y = Operation("getarg", [Constant(1)])
        a = SourceBit(x, 3)
        assert xor_bits(a, 1) == xor_bits(1, a) == invert_bit(a)
        assert xor_bits(a, 0) == xor_bits(0, a) == a
        assert xor_bits(a, a) == 0
        assert xor_bits(a, invert_bit(a)) == 1

        # positions disagree
        assert xor_bits(a, SourceBit(x, 4)) is None

        # sources disagree
        assert xor_bits(a, SourceBit(y, 3)) is None
        assert xor_bits(a, SourceBit(y, 3, True)) is None


    def test_xor():
        x = Operation("getarg", [Constant(0)])
        y = Operation("getarg", [Constant(1)])
        absx = BitProvenance.from_source(x)
        absy = BitProvenance.from_source(y)

        # x ^ 0 == x
        result = Operation("int_xor", [x, Constant(0)])
        assert absx.abstract_xor(BitProvenance.from_constant(0), result) == absx

        # x ^ -1 == ~x
        result = Operation("int_xor", [x, Constant(INT_MASK)])
        assert absx.abstract_xor(BitProvenance.from_constant(INT_MASK), result) == absx.abstract_invert()

        # x ^ x == 0
        result = Operation("int_xor", [x, x])
        assert absx.abstract_xor(absx, result).get_constant() == 0

        # x ^ y: we can't usefully represent provenance, so we get fresh bits
        result = Operation("int_xor", [x, y])
        assert absx.abstract_xor(absy, result) == BitProvenance.from_source(result)

        # x ^ ~x == -1
        result = Operation("int_xor", [x, Operation("int_invert", [x])])
        assert absx.abstract_xor(absx.abstract_invert(), result).get_constant() == INT_MASK


    @given(ints, ints)
    def test_hypothesis_xor_on_constants(a, b):
        abs_a = BitProvenance.from_constant(a)
        abs_b = BitProvenance.from_constant(b)
        result = Operation("int_xor", [Constant(a), Constant(b)])
        assert abs_a.abstract_xor(abs_b, result).get_constant() == a ^ b


    class BitProvenance:
        ...

        def abstract_xor(self, other, result: Operation):
            bits = []
            for i, (bit_a, bit_b) in enumerate(zip(self.bits, other.bits)):
                bit_res = xor_bits(bit_a, bit_b)
                if bit_res is None:
                    # not representable, use fresh provenance
                    bit_res = SourceBit(result, i)
                bits.append(bit_res)
            return BitProvenance.make(bits)


Extracting Simpler Operations
-----------------------------

Now that we have the analysis, we need to find out how to use the information
during optimization. We'll discuss four ways of doing that, from easy to more complicated.




Constants
+++++++++

The simplest thing to do is to exploit the fact that provenance can also
identify constant results.

.. code:: python

    def test_constant_via_provenance():
        bb = Block()
        x = bb.getarg(0)
        a = bb.int_and(x, 0x0f)
        b = bb.int_or(x, 0xf0)
        c = bb.int_and(b, 0x0f)
        # we compute result = (x & 0x0f) ^ ((x | 0xf0) & 0x0f)
        # ((x | 0xf0) & 0x0f) can be rewritten to
        # (x & 0x0f) | (0xf0 & 0x0f)
        # which is x & 0x0f
        # this means result == (x & 0x0f) ^ (x & 0x0f) == 0
        result = bb.int_xor(a, c)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = dummy(0)"""

To make this test pass, we can do something very similar to what we did in the
`KnownBits post`_. We go along a basic block, apply the transfer functions, and if
a result is constant we can replace the operation with that constant.

.. code:: python

    def unknown_transfer_functions(*abstract_args, result):
        return BitProvenance.from_source(result)

    def simplify(bb: Block) -> Block:
        abstract_values = {} # dict mapping Operation to BitProvenance

        def provenance_of(val : Value):
            if isinstance(val, Constant):
                return BitProvenance.from_constant(val.value)
            return abstract_values[val]

        opt_bb = Block()
        for op in bb:
            # apply the transfer function on the abstract arguments
            name_without_prefix = op.name.removeprefix("int_")
            method_name = f"abstract_{name_without_prefix}"
            transfer_function = getattr(BitProvenance, method_name, unknown_transfer_functions)
            abstract_args = [provenance_of(arg.find()) for arg in op.args]
            abstract_res = abstract_values[op] = transfer_function(*abstract_args, result=op)
            # if the result is a constant, we optimize the operation away and make
            # it equal to the constant result
            const = abstract_res.get_constant()
            if const is not None:
                op.make_equal_to(Constant(const))
                continue
            # otherwise emit the op
            opt_bb.append(op)
        return opt_bb

Identity
+++++++++

The next optimization we can add is that sometimes complicated bit reshuffling
leads to a result that was already computed earlier in the block. We can start
with a simple test that splits a value into low and high bits and recombines them:


.. code:: python

    def test_identity_by_recombining_bits():
        # split and then recombine x
        # lo = x & 0x0f
        # hi = (x >> 4) << 4
        # result = lo | hi
        bb = Block()
        x = bb.getarg(0)
        lo = bb.int_and(x, 0x0f)
        shifted = bb.int_rshift(x, 4)
        hi = bb.int_lshift(shifted, 4)
        result = bb.int_or(lo, hi)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = dummy(optvar0)"""

To help implement this, we can add a method to check whether a provenance is
identical to that of an earlier result. The idea is that if the bits of a
``BitProvenance`` come from bits ``0, 1, 2, ..., INTEGER_WIDTH - 1`` of the same source,
without inversion, then the operation we are looking at computes the same result
as the source too.

.. code:: python

    def test_provenance_get_identical_source():
        source = Operation("getarg", [Constant(0)])
        x = BitProvenance.make([1, 0, SourceBit(source, 1, True), SourceBit(source, 0)])
        assert x.get_identical_source() is None # not the same value as source

        # trivially, a BitProvenance where we know nothing is a valid source for itself
        res = BitProvenance.from_source(source)
        assert res.get_identical_source() is source


    class BitProvenance:
        ...
        def get_identical_source(self) -> Operation | None:
            bit0 = self.bits[0]
            if isinstance(bit0, int):
                return None # a constant bit cannot match an unconstrained source bit
            source = bit0.source
            # are all the bits the same as in the unconstrained source?
            if self == BitProvenance.from_source(source):
                return source
            return None


Now we can use that to recognize identities when optimizing:

.. code:: python
    :emphasize-lines: 23,24,25,26

    def simplify(bb: Block) -> Block:
        abstract_values = {} # dict mapping Operation to BitProvenance

        def provenance_of(val : Value):
            if isinstance(val, Constant):
                return BitProvenance.from_constant(val.value)
            return abstract_values[val]

        opt_bb = Block()
        for op in bb:
            # apply the transfer function on the abstract arguments
            name_without_prefix = op.name.removeprefix("int_")
            method_name = f"abstract_{name_without_prefix}"
            transfer_function = getattr(BitProvenance, method_name, unknown_transfer_functions)
            abstract_args = [provenance_of(arg.find()) for arg in op.args]
            abstract_res = abstract_values[op] = transfer_function(*abstract_args, result=op)
            # if the result is a constant, we optimize the operation away and make
            # it equal to the constant result
            const = abstract_res.get_constant()
            if const is not None:
                op.make_equal_to(Constant(const))
                continue
            source = abstract_res.get_identical_source()
            if source is not None and source is not op:
                op.make_equal_to(source)
                continue
            # otherwise emit the op
            opt_bb.append(op)
        return opt_bb


Reusing Earlier Values
+++++++++++++++++++++++++++


The motivating example from the start of the blog post is next. It doesn't
quite work with the idea from the previous subsection. Here it is in test form:


.. code:: python

    def test_identity_via_provenance():
        bb = Block()
        x = bb.getarg(0)
        a = bb.int_and(x, 0x0f)
        b = bb.int_lshift(x, 60)
        c = bb.int_rshift(b, 60)
        # result is same as a, but the bits come from x
        result = bb.int_and(a, c)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = int_and(optvar0, 15)
    optvar2 = dummy(optvar1)"""

We will use a hashmap to store all the provenance patterns we have seen in the
basic block so far.

.. code:: python
    :emphasize-lines: 3,24,25,26,27,28,29

    def simplify(bb: Block) -> Block:
        abstract_values = {} # dict mapping Operation to BitProvenance
        seen_provenances = {} # dict mapping BitProvenance to Value

        def provenance_of(val : Value):
            if isinstance(val, Constant):
                return BitProvenance.from_constant(val.value)
            return abstract_values[val]

        opt_bb = Block()
        for op in bb:
            # apply the transfer function on the abstract arguments
            name_without_prefix = op.name.removeprefix("int_")
            method_name = f"abstract_{name_without_prefix}"
            transfer_function = getattr(BitProvenance, method_name, unknown_transfer_functions)
            abstract_args = [provenance_of(arg.find()) for arg in op.args]
            abstract_res = abstract_values[op] = transfer_function(*abstract_args, result=op)
            # if the result is a constant, we optimize the operation away and make
            # it equal to the constant result
            const = abstract_res.get_constant()
            if const is not None:
                op.make_equal_to(Constant(const))
                continue
            # check whether we've seen the provenance before, if yes, reuse the op
            source = seen_provenances.get(abstract_res)
            if source is not None:
                op.make_equal_to(source)
                continue
            seen_provenances[abstract_res] = op
            # otherwise emit the op
            opt_bb.append(op)
        return opt_bb



Simple Shifts
+++++++++++++++++++++++++++

In addition to using existing values, we can sometimes emit a new shift
operation of some earlier value, to get fewer operations than how the value was
actually computed. Here's an example:

.. code:: python

    def test_extract_rshift_from_source():
        bb = Block()
        x = bb.getarg(0)
        # lo = (x & 0xf)
        lo = bb.int_and(x, 0x0f)
        # cleared = x ^ (x & 0xf)
        cleared = bb.int_xor(x, lo)
        # result = cleared >> 4
        result = bb.int_rshift(cleared, 4)
        bb.dummy(result)

        # the xor clears only the bits that the shift discards
        # the result's provenance matches a direct x >> 4
        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = int_rshift(optvar0, 4)
    optvar2 = dummy(optvar1)"""


To implement this, we add a new method ``BitProvenance.recognize`` which
detects whether a ``BitProvenance`` instance could be represented as a shift of
the source.

.. code:: python

    def test_recognize_rshift():
        x = Operation("getarg", [Constant(0)])
        # low bits come from x[4], x[5], ..., x[63]; the high four are zero
        bits = tuple(SourceBit(x, i) for i in range(4, INTEGER_WIDTH))
        shifted = BitProvenance.make(bits + (0, 0, 0, 0))
        assert shifted.recognize() == ("int_rshift", x, 4)

        # the same alignment is not enough if a high bit is one
        not_a_shift = BitProvenance.make(bits + (0, 0, 0, 1))
        assert not_a_shift.recognize() is None

        # the first bit suggests >> 4, but the next bit comes from x[6], not x[5]
        misplaced = bits[:1] + (SourceBit(x, 6),) + bits[2:]
        not_a_shift = BitProvenance.make(misplaced + (0, 0, 0, 0))
        assert not_a_shift.recognize() is None


    @given(strategies.integers(1, 63))
    def test_hypothesis_recognize_shift(shift):
        x = Operation("getarg", [Constant(0)])
        absval = BitProvenance.from_source(x)
        shift_amount = BitProvenance.from_constant(shift)
        # check that lshifts are recognized
        result = Operation("int_lshift", [x, Constant(shift)])
        res = absval.abstract_lshift(shift_amount, result).recognize()
        assert res == ("int_lshift", x, shift)

        # check that rshifts are recognized
        result = Operation("int_rshift", [x, Constant(shift)])
        res = absval.abstract_rshift(shift_amount, result).recognize()
        assert res == ("int_rshift", x, shift)

    class BitProvenance:
        ...
        def recognize(self):
            # return None or a triple (opname, source, shift amount), where
            # opname is "int_rshift" or "int_lshift"
            bits = [(i, b) for i, b in enumerate(self.bits) if isinstance(b, SourceBit)]
            if not bits:
                return None
            # try to guess the shift amount
            i, b = bits[0]
            delta = i - b.index
            source = b.source
            original = BitProvenance.from_source(source)
            # use the transfer functions to check whether it really is that shift
            if delta >= 0:
                expected = original.abstract_lshift(BitProvenance.from_constant(delta), None)
                # does the shift of the source match self?
                if self == expected:
                    return ("int_lshift", source, delta)
            else:
                expected = original.abstract_rshift(BitProvenance.from_constant(-delta), None)
                # does the shift of the source match self?
                if self == expected:
                    return ("int_rshift", source, -delta)
            return None

Using the abstract transfer functions in ``recognize`` has the nice effect that
we only specify what ``lshift`` and ``rshift`` do in a single place.

Now we can start using this in ``simplify``:

.. code:: python
    :emphasize-lines: 30,31,32,33,34,35,36,37,38,39,40,42

    def simplify(bb: Block) -> Block:
        abstract_values = {} # dict mapping Operation to BitProvenance
        seen_provenances = {} # dict mapping BitProvenance to Value

        def provenance_of(val : Value):
            if isinstance(val, Constant):
                return BitProvenance.from_constant(val.value)
            return abstract_values[val]

        opt_bb = Block()
        for op in bb:
            # apply the transfer function on the abstract arguments
            name_without_prefix = op.name.removeprefix("int_")
            method_name = f"abstract_{name_without_prefix}"
            transfer_function = getattr(BitProvenance, method_name, unknown_transfer_functions)
            abstract_args = [provenance_of(arg.find()) for arg in op.args]
            abstract_res = abstract_values[op] = transfer_function(*abstract_args, result=op)
            # if the result is a constant, we optimize the operation away and make
            # it equal to the constant result
            const = abstract_res.get_constant()
            if const is not None:
                op.make_equal_to(Constant(const))
                continue
            # check whether we've seen the provenance before, if yes, reuse the op
            source = seen_provenances.get(abstract_res)
            if source is not None:
                op.make_equal_to(source)
                continue

            # now try to synthesize a shift with the same provenance
            pattern = abstract_res.recognize()
            if pattern is not None:
                name, source_op, shift_amount = pattern
                if source_op is not op:
                    assert shift_amount > 0 # otherwise one of the earlier rules would have caught it
                    new_op = getattr(opt_bb, name)(source_op, Constant(shift_amount))
                    abstract_values[new_op] = abstract_res
                    seen_provenances[abstract_res] = new_op
                    op.make_equal_to(new_op)
                    continue
            # otherwise emit the op
            seen_provenances[abstract_res] = op
            opt_bb.append(op)
        return opt_bb

That's the whole optimizer. We propagate where each bit comes from, then look
for a cheaper way to produce the resulting provenance. Constant folding, reuse
of earlier values, and shift recognition all use the same information. None of
them needs to know which sequence of operations produced it.

More Rewrites from the Same Rules
++++++++++++++++++++++++++++++++++++++

Now we can look at a few other rewrites that fall out of this design. Here are
some further passing tests:

.. code:: python

    def test_xor_masks_cancel():
        bb = Block()
        x = bb.getarg(0)
        # each low-byte bit is flipped twice: 0x55 ^ 0xff ^ 0xaa == 0
        # therefore (((x ^ 0x55) ^ 0xff) ^ 0xaa) == x
        # by constant reassociation
        a = bb.int_xor(x, 0x55)
        b = bb.int_xor(a, 0xff)
        result = bb.int_xor(b, 0xaa)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = dummy(optvar0)"""


    def test_recover_low_bits_after_packing_two_sources():
        bb = Block()
        x = bb.getarg(0)
        y = bb.getarg(1)
        lo = bb.int_and(x, 0xff)
        hi = bb.int_lshift(y, 8)
        packed = bb.int_or(lo, hi)
        # masking the packed value recovers the earlier low byte of x
        result = bb.int_and(packed, 0xff)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = int_and(optvar0, 255)
    optvar2 = dummy(optvar1)"""


    def test_reuse_mask_via_de_morgan():
        bb = Block()
        x = bb.getarg(0)
        masked = bb.int_and(x, 0x0f)
        inverted = bb.int_invert(x)
        high_ones = bb.int_or(inverted, INT_MASK ^ 0x0f)
        # ~(~x | ~0x0f) == x & 0x0f, which we already computed
        result = bb.int_invert(high_ones)
        bb.dummy(masked, result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = int_and(optvar0, 15)
    optvar2 = dummy(optvar1, optvar1)"""

    def test_byte_swap_twice():
        def byte_swap(bb, value):
            result = 0
            for byte_index in range(8):
                byte = bb.int_and(bb.int_rshift(value, byte_index * 8), 0xff)
                moved = bb.int_lshift(byte, (7 - byte_index) * 8)
                result = bb.int_or(result, moved)
            return result

        bb = Block()
        x = bb.getarg(0)
        # little-endian host to network byte order, then back to host order
        network_order = byte_swap(bb, x)
        result = byte_swap(bb, network_order)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = dummy(optvar0)"""


Here's an even more complicated test. It reverses the bits of the argument,
then shifts left by 7, then reverses the bits of the result again. The input
block has 63 operations, and ``dce(simplify(bb))`` reduces it to just three. The
bit reversal below is adapted from `Hacker's Delight`_, section 7-1.

.. code:: python

    def test_reverse_lshift_reverse_becomes_rshift():
        # Hacker's Delight, section 7-1: swap adjacent bits, then pairs,
        # nibbles, bytes, and larger fields. adapted from 32 to 64 bits
        def reverse_bits(bb, value):
            for shift, mask in [
                (1,  0x5555555555555555),
                (2,  0x3333333333333333),
                (4,  0x0f0f0f0f0f0f0f0f),
                (8,  0x00ff00ff00ff00ff),
                (16, 0x0000ffff0000ffff),
                (32, 0x00000000ffffffff),
            ]:
                # value = ((value & mask) << shift) | ((value >> shift) & mask)
                left = bb.int_lshift(bb.int_and(value, mask), shift)
                right = bb.int_and(bb.int_rshift(value, shift), mask)
                value = bb.int_or(left, right)
            return value

        bb = Block()
        x = bb.getarg(0)
        reversed_once = reverse_bits(bb, x)
        shifted = bb.int_lshift(reversed_once, 7)
        result = reverse_bits(bb, shifted)
        bb.dummy(result)

        opt_bb = dce(simplify(bb))
        # reversing before and after a left shift turns it into a right shift
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = int_rshift(optvar0, 7)
    optvar2 = dummy(optvar1)"""

What I like about all of these is how quite varied operation rewrites just fall
out from the bit provenance approach, without needing complicated peephole
rewrite patterns.



Evaluation with Pydrofoil and PyPy
------------------------------------

To evaluate the bit provenance optimizer, I wrote a program that applies it to
PyPy JIT traces. I didn't fully build it into the PyPy JIT because I was quite
skeptical that it would help. Instead, I wrote an external optimization pass
that parses RPython JIT logs, applies the optimization and then produces
statistics. This uses an extended prototype that supports additional operations
such as arithmetic right shifts and sign extension, and can extract shifts of
earlier computed values as well as shifts of the original source.

I did this experiment for two different RPython projects, for PyPy (running the
translator, that bootstraps PyPy to C code) and Pydrofoil_ (RISC-V simulation
based on Sail_, booting the Linux kernel). I picked the latter because Pydrofoil
does a lot of integer operations, whereas most Python code does very little.

For both of these programs I wanted to know how well the bit provenance
optimizer can optimize the traces compared to the integer optimizations of the
PyPy JIT. I took the unoptimized traces, removed everything but integer
operations and performed dead code elimination. To do that, the integer results
of non-pure operations are turned into unconstrained arguments of the trace.
Integer values used by removed operations are retained as outputs. The
remaining integer operations are our baseline traces for this experiment.

The following table shows the results. The first column shows the number of
unoptimized integer operations. The second column shows how many operations are
left after running just bit provenance optimizations. The third column shows
how many operations are left after the RPython JIT integer optimizations run.
The last column shows how many operations are left after we run first the
RPython JIT optimizer and then bit provenance optimizations. All three paths
include dead code elimination after optimization.

In parentheses are the percentages of how many of the unoptimized operations
are removed by the corresponding path.

.. class:: table table-bordered table-sm

========== ============ ===================== ===================== ========================
Workload    Unoptimized           Provenance              RPython   RPython then Provenance
========== ============ ===================== ===================== ========================
Pydrofoil     1,484,985      822,864 (44.59%)     769,758 (48.16%)      656,555 (55.79%)
PyPy          1,442,782    1,374,803 ( 4.71%)   1,089,196 (24.51%)    1,089,196 (24.51%)
========== ============ ===================== ===================== ========================

The 'RPython then Provenance' column shows that, for the PyPy workload,
provenance removes no additional operations after the RPython integer
optimization passes in this experiment. For Pydrofoil it does remove more
operations, but we will have to investigate whether this benefit carries over
to the full JIT optimization pipeline.

However, the comparison between the  'Provenance' and 'RPython' column for
Pydrofoil shows that the design of the optimizer is quite good! The small
provenance optimizer achieves nearly as much reduction in integer operation
count as the complicated and well-tuned integer optimization passes of the
RPython JIT.

Related work
----------------------------

LLVM has a very similar bit provenance tracking optimization as part of the
Hexagon_ backend. It also tracks 0 bits, 1 bits or references to specific bits
from other SSA operations (it doesn't track negation). It is split into the
``BitTracker`` analysis__ and the ``HexagonBitSimplify`` `optimization pass`__.

.. __: https://llvm.org/doxygen/BitTracker_8cpp_source.html
.. __: https://llvm.org/doxygen/HexagonBitSimplify_8cpp_source.html

LLVM also has ``collectBitParts`` (source__). Rather than running a separate
forward analysis, it recursively walks SSA operations following provenance
(with memoization and limited recursion depth for performance). Then there is a
check whether the resulting provenance describes a byte swap or bit reversal.

.. __: https://llvm.org/doxygen/Transforms_2Utils_2Local_8cpp_source.html#l03503

In GCC this tracking happens on a byte level to be able to recognize byte swaps
in the `byte-swap recognizer`__. It also tracks memory addresses and offsets to
recognize wider loads assembled from separate byte loads, possibly with a byte
swap. However, there's also a recent (as of writing unmerged) `patch series`__
to extend this to bit granularity.

.. __: https://github.com/gcc-mirror/gcc/blob/master/gcc/gimple-ssa-store-merging.cc
.. __: https://www.mail-archive.com/gcc-patches%40gcc.gnu.org/msg419161.html


Conclusion
-----------------

The interesting result here isn't that we beat an existing optimizer. It's
that a handful of transfer functions lets us discover rewrites across
arbitrarily long chains of bit operations, without writing a rule for each
combination. The evaluation suggests that existing integer optimizations
already cover much of this stuff. However, bit provenance gives us a compact
way to describe a whole family of simplifications. It's quite cool to write an
optimizer that can undo a bit reversal without ever knowing what a bit reversal
is.

The entire code can be found in this gist__.

.. __: https://gist.github.com/cfbolz/b05d4796e1861be1d0f6aea59d1ab33b

Acknowledgements
-----------------

Thanks to Joe Groff for the `fantastic title`_. Thanks to Can Joshua Lehmann,
Andy Wingo, Matti Picus, and Nico Rittinghaus for feedback on the draft, and to
Max Bernstein for encouragement.


.. _Knownbits Toy abstract domain: https://pypy.org/posts/2024/08/toy-knownbits.html
.. _peephole rewrite rules: https://pypy.org/posts/2024/10/jit-peephole-dsl.html
.. _KnownBits post: https://pypy.org/posts/2024/08/toy-knownbits.html
.. _abstract domain: https://bernsteinbear.com/blog/toy-abstract-interpretation/
.. _toy optimizer: https://pypy.org/posts/2022/07/toy-optimizer.html
.. _previous posts: https://pypy.org/categories/toy-optimizer.html
.. _Prospero blog post: https://pypy.org/posts/2025/04/prospero-in-rpython.html#dead-code-elimination
.. _Hypothesis: https://hypothesis.readthedocs.io/en/latest/quickstart.html
.. _Hacker's Delight: https://www.oreilly.com/library/view/hackers-delight-second/9780133084993/contents.html
.. _Pydrofoil: https://github.com/pydrofoil/pydrofoil
.. _Sail: https://github.com/rems-project/sail
.. _SSA: https://en.wikipedia.org/wiki/Static_single-assignment_form
.. _Hexagon: https://en.wikipedia.org/wiki/Qualcomm_Hexagon
.. _`fantastic title`: https://f.duriansoftware.com/@joe/117496240838231720 
