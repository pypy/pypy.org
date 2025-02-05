.. title: Optimizations in Pydrofoil
.. slug: optimizations-pydrofoil
.. date: 2025-02-10 11:00:00 UTC
.. tags: emulation,performance
.. category: pydrofoil,jit
.. link:
.. description:
.. type:
.. author: CF Bolz-Tereick


Since summer 2022 I have been working on and off on Pydrofoil, a jitting RISC-V
(and later ARM) emulator that is automatically generated out of the
specification for these instruction sets (together with Martin Berger, John
Witulski, Matti Picus, Jubo Xu, Ryan Lin, and others). I have written [very
little](/posts/2023/05/rpython-used-to-speed-up-risc-v-simulation-over-15x.txt)
about it, so in this post I wanted to explain the architecture of Pydrofoil a
little bit better, how some of the optimizations that I have implemted for it
work, and explore which of the optimizations help how much.


# Background: Sail and the RISC-V model

[Sail](https://github.com/rems-project/sail/) is a DSL for describing very
precisely how an instruction set architecture of a CPU behaves. Having a precise
description of what an instruction set is supposed to do is quite valuable, as
it provides a contract between the software and the hardware, that both sides
(ideally) can rely on in all situations. Such a description could be used to
test CPU designs against this specification, as well as testing whether a
compiler backend produces correct code.

The [RISC-V specification](https://github.com/riscv/sail-riscv) is written using
the Sail DLS and was adopted by RISC-V International as the official spec of the
ISA.

Sail is "a first-order imperative language, but with lightweight dependent
typing for numeric types and bitvector lengths, which are automatically checked
using the Z3 SMT solver." It has a bitvector type and arbitrary precision
integers. It also has a number of features inspired by functional languages
such as sum types and pattern matching (including over bitvectors).

We won't go into the details of the language too much, but here's an example
specifying what happens when an `ITYPE` instruction (ie an instruction with an
immediate) in RISC-V is executed:

```
scattered union ast

val execute : ast -> Retired
scattered function execute

val encdec : ast <-> bits(32)
scattered mapping encdec

union clause ast = ILLEGAL : word
```

First some type declarations: The `union ast` is the union type that represents
a decoded instruction. (Aside: I personally find using the term "AST" pretty
confusing here, because decoded instructions aren't tree-like at all, and they
aren't really "syntax" either). It's a `scattered` union, which means that the
variants can be defined sprinkled across many source code files. The function
`execute` (also scattered) takes an `ast` and returns `Retired`, which is an
enum specifying whether the instruction successfully executed or not. To map
between the encoding of instructions into bits and the more structured
representation of an `ast`, there's the (scattered) mapping `encdec`. A mapping
is a bidirectional function, meaning that you can use it to either take an `ast`
value and encode it into 32-bit bitvector, or take a bitvector and decode it
into an `ast`.

The following are the relevant clauses of `ast`, `encdec` and `execute` for the
`ITYPE` group of instructions, which all take an immediate:

```
enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU,
            RISCV_XORI, RISCV_ORI, RISCV_ANDI}    /* immediate ops */

...

union clause ast = ITYPE : (bits(12), regidx, regidx, iop)
```

The `ITYPE` variant of the `ast` type contains a 12-bit bitvector (the immediate
value), two register indexes (source and destination), and an `iop` enum to
specify which `ITYPE` instruction it is.

Now we get to specifying how `ITYPE` are encoded into bits using bidirectional
mapping functions:

```
mapping encdec_iop : iop <-> bits(3) = {
  RISCV_ADDI  <-> 0b000,
  RISCV_SLTI  <-> 0b010,
  RISCV_SLTIU <-> 0b011,
  RISCV_ANDI  <-> 0b111,
  RISCV_ORI   <-> 0b110,
  RISCV_XORI  <-> 0b100
}

mapping clause encdec = ITYPE(imm, rs1, rd, op)
  <-> imm @ rs1 @ encdec_iop(op) @ rd @ 0b0010011
```

The `@` operator is used for concatenating bitvectors, so the right-hand side of
`encdec` is doing pattern matching on the `bits(32)` bitvector type to extract
the necessary information for an `ITYPE` value of the `ast` type (or to
construct the resulting bitvector when running `encdec` in the other direction).

Finally we get to how to execute an `ITYPE` instruction:

```
function clause execute (ITYPE (imm, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let immext : xlenbits = sign_extend(imm);
  let result : xlenbits = match op {
    RISCV_ADDI  => rs1_val + immext,
    RISCV_SLTI  => zero_extend(bool_to_bits(rs1_val <_s immext)),
    RISCV_SLTIU => zero_extend(bool_to_bits(rs1_val <_u immext)),
    RISCV_ANDI  => rs1_val & immext,
    RISCV_ORI   => rs1_val | immext,
    RISCV_XORI  => rs1_val ^ immext
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
```

First we load the value of the source register. Then we sign-extend the
immediate value to the register width (`xlenbits` is either 32 or 64 bits,
depending on the RISC-V variant, the specification covers both of them at once).
Otherwise we perform the actual operation with the value of the source register
and the sign-extended immediate, depending on the `op` enum value. Afterwards we
write the result into the destination register and retire the instruction.

We will use the `execute` clause of `ITYPE` instructions as a running example in
the rest of the post.

## Why is Sail slow

There's a number of tools that use the specification of an ISA around the Sail
language. For example, Sail code can be compiled into Rocq in order to perform
proofs of properties of the specification. The backend that interests me
personally the most is the C backend. It can be used to turn the Sail model into
an interpreter for the ISA. The Sail model of RISC-V is fairly complete, so the
resulting interpreter can then be used to run various RISC-V binaries, including
test suites and small baremetal programs. It's also complete enough to boot
Linux and then run programs in user space.

Unfortunately the interpreters that the C backend of Sail generates are rather
slow. Sail-RISC-V execute about 400,000 instructions per second on my laptop.
The reason for that is twofold: on the one hand Sail is quite a high-level
language that is much more focused on clearly expressing the semantics of the
ISA over being able to emulate it quickly. On the other hand there simply hasn't
been a lot of effort put into making the C code that Sail generates more
efficient, the Sail team has simply worked more on other areas.

Let's look at some concrete C code that the backend generates to understand why
this is the case. The following is the C code that Sail generates from the
`execute` clause of `ITYPE` instructions. I've lightly edited the code to make
it simpler to read and added the Sail code as comments before the corresponding
C code lines.

```c
...
  {
    uint64_t imm = ...;
    ...
    // let rs1_val = X(rs1);
    uint64_t rs1_val;
    rs1_val = zrX_bits(rs1);
    // let immext : xlenbits = sign_extend(imm);
    uint64_t immext;
    {
      sail_int sail_int_64;
      CREATE(sail_int)(&sail_int_64);
      CONVERT_OF(sail_int, mach_int)(&sail_int_64, INT64_C(64));
      lbits imm_lbits;
      CREATE(lbits)(&imm_lbits);
      CONVERT_OF(lbits, fbits)(&imm_lbits, imm, UINT64_C(12) , true);
      lbits immext_lbits;
      CREATE(lbits)(&immext_lbits);
      zsign_extend(&immext_lbits, sail_int_64, imm_lbits);
      immext = CONVERT_OF(fbits, lbits)(immext_lbits, true);
      KILL(lbits)(&immext_lbits);
      KILL(lbits)(&imm_lbits);
      KILL(sail_int)(&sail_int_64);
    }
    uint64_t result;
    {
      __label__ case_8084, case_8085, case_8086, case_8087, case_8088, case_8089, finish_match_8083;

      /* Case with num_cases: 6 */
      {
        if ((zRISCV_ADDI != op)) goto case_8084;
        result = ((rs1_val + immext) & UINT64_C(0xFFFFFFFFFFFFFFFF));
        goto finish_match_8083;
      }
    case_8084: ;
      ... // the other cases
    }
    {
      unit zgsz38132;
      zgsz38132 = zwX_bits(rd, result);
    }
    zcbz31056 = zRETIRE_SUCCESS;
    goto finish_match_8062;
  }
```

While the actual computation of the result in the `ADDI` case is nicely mapped
to an addition on the host machine, the sign extension of the 12-bit immediate
is done with a call to the function `zsign_extend`. The arguments of this call
are of type `lbits`, which is a heap-allocated data structure storing bitvectors
of arbitrary size. To be able to call `sign_extend`, the variable `imm` needs to
be converted to type `lbits`, which requires a call to `malloc` as part of the
`CONVERT_OF` macro. Similarly, the `sail_int` is also heap allocated and
represents integers of arbitrary division. Both `lbits` and `sail_int` use the
GMP library to represent bit bitvectors/integers.


More generally, here are three reasons why the emulator that Sail generates is
slow:

**Bitvectors**: Sail tries to infer the bitwidth of the bitvector variables in
the program. If they are statically known to fit into a machine word, the C
backend will map them to C integer types. However, a lot of functions in a Sail
spec are typically written to be independent of the width of the integer types.
The bitvectors in these functions are implemented using `lbits` and thus
ultimately GMP integers. This has a number of drawbacks. It means that all
operations on these bitvectors require (de-)allocations, because GMP ints are
always heap-allocated.

**Integers**: The integer type in Sail has arbitrary precision. Again, Sail
has an analysis to find out whether some specific integer variables can only
have values that fit into a word-sized integer. For these integer variables the
C backend will then pick a C integer type. However, for all other integer
variables in the Sail program the C backend uses GMP to store them, which
requires constant allocations on all the machine operations.

**Interpretation Overhead**: And then there's of course the fundamental problem
that the emulator that Sail generates is an interpreter which has to re-analyze
the bits of the executed program again and again.

We want to improve all three of these problems in Pydrofoil.

# Architecture

Pydrofoil reuses RPython and the RPython JIT to generate faster emulators from
Sail models. The idea is to use the Sail model for some instruction set
architecture as the input and then produce an RPython-based jitted emulator from
the same input. The hope is to get much better emulation performance out of the
result, by optimizing the Sail code better at build time, picking better data
structures for bitvectors and integer types in the Sail language and also by
using the tracing JIT compiler of RPython.

I reuse as much of the front-end and type checker of Sail as possible by using
the JIB textual intermediate representation that another Sail-based project
([ISLA](https://github.com/rems-project/isla)) has implemented. When turning a
Sail model into JIB, all type checking has been done, all variables have
explicit types and all pattern matching is compiled away into basic blocks and
(conditional) gotos. This makes JIB easy to parse and easy to do further work
with.

After parsing the JIB code, Pydrofoil generates its own SSA-based intermediate
representation for Sail functions. Those functions are then further optimized by
Pydrofoil's static optimization passes. Then Pydrofoil generates RPython source
code from the optimization IR. The generated code makes use of Pydrofoil's
runtime library of support functions that implement the Sail datatypes, such as
bitvectors, integers, reals. The support library also implements the emulated
RAM. This RPython code can be tested by running it on a normal Python2
implementation. Or it can be further translated into a binary with the RPython
translation toolchain. During this process, a tracing JIT compiler can be
(optionally) inserted into the resulting binary. In the following sections we'll
go through these steps in detail.

# Parsing JIB and generating control flow graphs

Parsing the JIB code is straightforward, and so is generating SSA-based control
flow graphs from them. The control flow graphs consist of basic blocks and
(conditional) jumps between them. Here's a screenshot of the constructed CFG of
the `execute` clause of `ITYPE` instructions:

![itype flow graph](images/2025-pydrofoil-itype-before.svg)

# Static Pydrofoil IR Optimizations

After the SSA-based IR was generated from the parsed JIB code, a number of
standard compiler optimizations are performed on it:

- constant folding
- dead code elimination
- common subexpression elimination
- inlining
- scalar replacement of aggregates (using a simple form of partial escape
  analysis)

All of these are fairly standard, I won't talk too much about them here.

# Static Optimizations for BitVector and Integer operations

The most important static optimization are local rewrites to improve the cost of
bitvector and integer operations. JIB has two different kinds of static types
for each of these:

- there are bitvector types with statically known widths, eg `%bv64` and `%bv16`
- `%bv` is a generic bitvector type where the width isn't known at runtime
  (which turns into the `lbits` type we've seen in the Sail C backend code
  above)

For integers there are:

- `%i64` for integers that were inferred to always fit into a 64 bit signed
  machine integer
- ` %i` for arbitrary precision integers (which turns into `sail_int` in the C
  backend code we've seen above)

The JIB code contains a lot of casts between the two respective representations.

As we've discussed, the generic forms `%bv` and `%i` are much less efficient at
runtime. Since their size isn't known in advanced, values of these types need to
be allocated on the heap, and operations on them are also much less efficient
since they can't be directly mapped to operations on the host CPU.

Here's an example. The following JIB code corresponds to the beginning of
`ITYPE` `execute` fragment that we've been seen in Sail and C above. It's edited
it lightly for clarity.

```
fn zexecute(zmergez3var) {
...
  imm : %bv12
  imm = ...
  // let rs1_val = X(rs1);
  rs1_val : %bv64
  rs1_val = zrX_bits(rs1)
  // let immext : xlenbits = sign_extend(imm);
  immext : %bv64
  sail_int_64 : %i
  sail_int_64 = zz5i64zDzKz5i(64)
  imm_lbits : %bv
  imm_lbits = imm
  immext_lbits : %bv
  immext_lbits = zsign_extend(sail_int_64, imm_lbits)
  immext = immext_lbits
...
```

In this example, to perform the `sign_extend`, the immediate value of type
`%bv12` is first cast to a generic bitvector, then sign-extended to 64 bits,
then the result is cast back to `%bv64`. Doing this sign extension alone by
default requires 3 allocations.

To optimize operations on generic bitvectors and integers, Pydrofoil's static
optimizer has a lot of local rewrite rules that inspects the IR of a function
locally and rewrites operations on these types to more efficient forms. Ideally
it tries to remove casts between generic and specific bitvector types (as well
as machine integers and arbitrary integers) and uses specialized operations on
the types if they are available in Pydrofoil's runtime library.

In the case of the `sign_extend` call above, it can be replaced by a version
of the function that takes a `%bv12` and a `%i64` as argument and returns a
`%bv64`, getting rid of all three allocations.

To be able to narrow the generic integer type `%i` to the machine-word-sized
type `%i64`, Pydrofoil also performs a range analysis. If the analysis finds an
integer variable where the range fits into that of a machine word, Pydrofoil
narrows the type to `%i64`.

## Interaction with Inlining

Inlining helps tremendously to make bitvector and integer operation rewrites
more effective. Many small functions operate on generic bitvectors and integers,
that are passed in as arguments. After inlining these small functions into the
contexts of where they are used, the concrete bitvector widths of the argument
can often be inferred and the bitvector operations in the inlined function be
specialized to smaller bitwidths.

We can look at another one of the `ITYPE` operations as an example for this. The
`SLTI` cases uses the `operator <_s`, to perform the signed comparison. It
is defined as follows in Sail:

```
val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
function operator <_s  (x, y) = signed(x) < signed(y)
```

This gets compiled to the following JIB code:

```
val zz8operatorz0zI_sz9 : (%bv, %bv) ->  %bool

fn zz8operatorz0zI_sz9(zx, zy) {
  // signed(x) < signed(y)
  zz40 : %i
  zz40 = zsigned(zx)
  zz41 : %i
  zz41 = zsigned(zy)
  return = zlt_int(zz40, zz41)
  end;
}
```

The code implements a signed comparison of bitvectors and operates on generic
bitvectors. In the concrete context where the function is called, the bitvector
sizes are mostly known. E.g. in the context of the `SLTI` instruction:

```
  jump @neq(zRISCV_SLTI, zz415090) goto 280
  // RISCV_SLTI  => zero_extend(bool_to_bits(rs1_val <_s immext)),
  zz415112 : %bv1
  zz415116 : %bool
  zz415117 : %bv
  zz415117 = rs1_val
  zz415118 : %bv
  zz415118 = immext
  zz415116 = zz8operatorz0zI_sz9(zz415117, zz415118)
  zz415112 = zbool_to_bits(zz415116)
  ...
```

The arguments to the operator call are cast from `%bv64` to `%bv`. After
inlining the operator, the `signed` calls can therefore be optimized to a
variant that takes a `%bv64` and returns an `%i64`, which then allows the the
`lt_int` function to be replaced by a version that operates on `%i64`. This
removes all allocations in this code sequence completely.

After inlining and bitvector/integer operation optimization the control flow
graph of the `execute` clause for `ITYPE` instructions looks like this:

![itype flow graph after optimizations](images/2025-pydrofoil-itype-after.svg)


# Function Specialization

In cases where a called function is too large to be inlined Pydrofoil tries to
specialize it to the specific bitvector widths and machine int types of its
arguments at the function's callsites. This would have happened for the
operator call above, if that function were too big.

The specializer will go over all the non-inlinable function calls in the program
and check whether any of the arguments are either constant, or the result of
casts from more specific types. For such calls, the target function will be
cloned into a more specific version, taking this information into account. The
cloned version can then be locally optimized with the newly available bitvector
sizes, constant values, etc.

Sometimes, as the result of specialization, the return type of a function can
also become more specific. This allows the caller of such a specialized function
to be optimized further.

# RPython code generation

After the Sail functions have been optimized, we generate RPython source code
from them. This is again quite straightforward, the only complexity is that the
IR flow graphs use basic blocks with (conditional) jumps between them. Pydrofoil
compiles that to the standard construction of a program counter variable and an
infinite loop with one condition for every basic block. Here's the the produced
RPython code of our running example:

```python
def zexecute_zITYPE(zmergez3var, machine, ):
    pc = 0
    while 1:
        if pc == 0:
            i_0_0 = Union_zast_zITYPE.convert(zmergez3var)
            i_0_1 = i_0_0.ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop0
            i_0_2 = i_0_0.ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop1
            i_0_3 = i_0_0.ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop2
            i_0_4 = i_0_0.ztuplez3z5bv12_z5bv5_z5bv5_z5enumz0zziop3
            # inlined zrX_bits
            return_0_7 = func_zrX(machine, supportcode.unsigned_bv(machine, i_0_2, 5))
            # inlined zsign_extend
            return_0_9 = supportcode.sign_extend_bv_i_i(machine, i_0_1, 12, 64)
            if Enum_ziop.zRISCV_ADDI == i_0_4:
                i_2_0 = supportcode.add_bits_bv_bv(machine, return_0_7, return_0_9, 64)
                pc = 2
                continue
            # pc = 3, inlined
            if Enum_ziop.zRISCV_SLTI == i_0_4:
                # inlined zz8operatorz0zI_sz9
                # inlined zbool_to_bits
                # inlined zbool_bits_forwards
                if (supportcode.signed_bv(machine, return_0_7, 64) < supportcode.signed_bv(machine, return_0_9, 64)):
                    i_2_0 = r_uint(0x000000000000001L)
                    pc = 2
                    continue
                i_2_0 = r_uint(0x000000000000000L)
                pc = 2
                continue
            ...
        if pc == 2:
            # inlined zwX_bits
            func_zwX(machine, supportcode.unsigned_bv(machine, i_0_3, 5), i_2_0)
            return Enum_zRetired.zRETIRE_SUCCESS
```

# Runtime Support Library

The static optimizations can remove the need for the generic heap-allocated
bitvector and integer types in a lot of cases, but not all of them. Therefore it
is important to pick efficient runtime representations for the generic types,
especially for generic integers (`%i` in JIB). In theory the generic integer
type can store arbitrarily large values. In practice, however, most of the
integer values in the RISC-V emulator fit into one or at most two machine words.
Our implementation of the generic integer type makes use of this fact. The type
has two different implementations, one for the case where the value of an
integer fits into a machine word, and then then generic case that can really
implement arbitrarily large integers. The decision which implementation is
chosen is deferred to integer value creation at runtime.

To get an idea of how this looks we will sketch the implementation of integer
subtraction in the RPython code that implements the Sail integer values. A Sail
integer value is represented by an instance of the RPython class `Integer`.
`Integer` has two subclasses, `SmallInteger` represents integer values that fit
into a signed machine word, and `BigInteger` which represents arbitrary integer
values using a list of word-sized digits.

Here's a rough sketch of the classes:

```python
class Integer:
    ...

class SmallInteger(Integer):
    def __init__(self, val):
        self.val = val # a machine integer

    ...

    def sub(self, other):
        if isinstance(other, SmallInteger):
            try:
                return SmallInteger(ovfcheck(self.val - other.val))
            except OverflowError:
                pass
        return self.tobigint().add(other)


class BigInteger(Integer):
    def __init__(self, data, sign):
        self.data = data # list of unsigned machine int forming the digits
        self.sign = sign # 0, 1 or -1

    ...

    def sub(self):
        ... # actual subtraction of arbitrarily-sized integers
```

Integer subtraction on two `SmallInteger` instances performs the subtraction of
the two contained machine integers and checks whether the result fits into a
machine integer still. If yes, a new instance of `SmallInteger` is returned,
otherwise we convert the two ints to a `BigInteger` and perform the subtraction
there.

# Adding a JIT compiler with RPython

To get from a purely interpretation based emulator to a more efficient system we
can use RPython's meta-tracing JIT compiler. It will trace the execution of
the Pydrofoil-RISC-V through one loop of the emulated guest program and turn the
resulting traces into host machine code. In this way, RPython's tracing JIT acts
as a trace-based dynamic binary translator for the emulated instruction set
architecture.

RPython's meta-tracing JIT needs a few annotations in the core execution loop of
the Sail model in question. In particular, the tracing JIT needs to know what
the core execution loop is, and which of the registers of the emulated machine
stores the program counter.

After doing that, we can look at the JIT trace that is generated for a single
RISC-V addi instruction:

```
...
i106 = getfield_gc_i(p1, field=x20)
...
# c.addi s4. 0x8
i144 = getarrayitem_gc_i(ConstPtr(ptr142), 26)
i146 = int_and(i144, 65535)
i148 = int_and(i144, 3)
i150 = int_eq(i148, 3)
guard_false(i150)
i152 = int_eq(i146, 1)
guard_false(i152)
i154 = uint_rshift(i146, 5)
i156 = int_and(i154, 1)
i158 = uint_rshift(i146, 6)
i160 = int_and(i158, 1)
i162 = int_lshift(i156, 1)
i163 = int_or(i162, i160)
i165 = uint_rshift(i146, 7)
i167 = int_and(i165, 15)
i169 = uint_rshift(i146, 11)
i171 = int_and(i169, 3)
i173 = int_lshift(i171, 2)
i174 = int_or(i173, i163)
i176 = int_lshift(i167, 4)
i177 = int_or(i176, i174)
i178 = int_is_zero(i177)
guard_false(i178)
i180 = uint_rshift(i146, 13)
i181 = int_is_zero(i180)
guard_true(i181)
i182 = int_is_zero(i148)
guard_false(i182)
i184 = int_and(i165, 31)
i186 = uint_rshift(i146, 12)
i188 = uint_rshift(i146, 2)
i190 = int_and(i188, 31)
i192 = int_lshift(i186, 5)
i193 = int_or(i192, i190)
i194 = int_is_zero(i193)
guard_false(i194)
i195 = int_is_zero(i184)
guard_false(i195)
i197 = int_eq(i148, 1)
guard_true(i197)
i199 = int_xor(i193, 32)
i201 = int_sub(i199, 32)
i203 = int_and(i201, 4095)
guard_value(i184, 20)
i206 = int_xor(i203, 2048)
i208 = int_sub(i206, 2048)
i209 = int_add(i106, i208)
i211 = int_add(i2, 2)
i213 = int_add(i0, 2)
setfield_gc(p1, i209, field=x20)
i215 = int_eq(i213, 10000)
guard_false(i215)
... # next guest instruction
```

The details of this trace are not important, just that it's really long, given
that it performs only a single guest addition. The problem is the
`getarrayitem_gc_i` instruction at the very start, which is the instruction
fetch from the emulated RAM. A large part of the trace is manipulating the
result of that memory read to do the instruction decoding. In the next section
we will look at an optimization how to get rid of those instruction decoding
trace instructions.

## Making the RAM emulation JIT-friendly

One big problem for the JIT compiler is that while it knows the concrete value
of the guest program counter, that is not actually enough in order to optimize
away the decoding of the instruction at that program counter. The reason for
that is that the content of the emulated RAM is obviously mutable, in general.

In practice, however, it's very rare for code to be self-mutating. After a
program has been loaded into RAM, those parts of memory mostly do not change any
more. We want the JIT to make use of that fact. To be able to do that, we track
the status of every word of the emulated RAM. Every word in emulated RAM can be
in one of three states: `status_default`, `status_immutable`, `status_mutable`.
All the words start out in `status_default` state. If a `status_default` word is
read or written, nothing special happens. However, if a `status_default` is read
from during instruction fetch, it transitions to `status_immutable`. The JIT
will constant-fold reads from `status_immutable` words and return the concrete
value of the stored bits in the word.

To still behave correctly in the face of self-modifying machine code, the
emulated RAM then adds a write barrier to notice modifications of
`status_immutable` words. When a `status_immutable` word is changed, the
generated host machine code is potentially no longer valid, because it was
generated under the assumption that `status_immutable` words are immutable.
Therefore all relevant host machine code is invalidated in such a situation, and
the modified word is marked as `status_mutable`. `status_mutable` are assumed to
potentially contain mutable code, so the JIT will never constant-fold reads on
them during host machine code generation.

Here's a state diagram of the various states and transitions a machine word can
be in:

![memory state transitions](images/2025-pydrofoil-mem-states.svg)

The result of this approach is that instruction fetch can mostly be
constant-folded to no machine code instructions at all: the program counter is
known to the tracing JIT at every point, reading from that point in memory is
a read from a `status_immutable` word and therefore constant folded to a
constant bit pattern. Afterwards, decoding of that bit-pattern can be constant
folded too.

For our example trace, this has the following effect:

```
i35 = getfield_gc_i(p1, field=x20)
...
# c.addi s4. 0x8
i44 = int_add(i35, 8)
i64 = int_add(i0, 2)
setfield_gc(p1, i44, field=x20)
i66 = int_eq(i64, 10000)
guard_false(i66)

```

Now the trace looks actually good! The `addi s4, 0x8` instruction is compiled to
a `int_add(..., 8)` instruction, which is its closest equivalent in the PyPy
trace IR. There are a few extra instructions around to read and write the value
of the register field in the `p1` struct, which contains the emulated machine's
state. In addition, there are three instructions that check whether 10000
instructions have been executed, which would make it time to tick the emulated
clock.


# Various other problems and future ideas

There are a number of known inefficiencies in Pydrofoil. I want to discuss a few
of them in this sections, together with ideas what to maybe do about
them.

## Clocks

The first inefficiency is that of clocks. The Sail model ticks the emulated
clock exactly every 100 instructions. This number was chosen at some point,
maybe somewhat arbitrarily. In Pydrofoil we made this number configurable but
mostly run benchmarks with a value of 10,000.

Having to check whether the next clock tick is reached in the generated host
machine code of every single guest instruction is quite inefficient. In addition
to the cost of the checks itself, there's also the problem of the JIT compiler
making code for all the control flow edges that go from every single instruction
to the clock tick logic.

There is existing [literature](https://dl.acm.org/doi/pdf/10.1145/2907950.2907953)
for how to improve this situation and I want to be able to find out whether I
can use some of the approaches described in Pydrofoil.

## Address translation

Another big source of inefficiency is address translation. If the emulated
program turns address translation on (like every operating system will
eventually do), every memory access goes through a page table walk in order to
map virtual addresses to physical addresses. This is very inefficient, since it
turns a single emulated RAM read into many emulated RAM reads.

The RISC-V Sail model has a [translation lookaside
buffer](https://en.wikipedia.org/wiki/Translation_lookaside_buffer) (TLB), which
is a cache that caches address translation. The presence of this cache helps
Pydrofoil a lot, but it even a successful cache lookup requires dozens of host
instructions in the generated traces.

There is also [emulation](https://www.diva-portal.org/smash/get/diva2:1041423/FULLTEXT01.pdf)
[literature](https://dl.acm.org/doi/10.1145/2837027) that describes techniques
for implementing virtual memory more efficiently in emulators, so I want to see
whether some of these could be used in Pydrofoil.


# Benchmarking various Pydrofoil variants

To understand how much the various described optimizations help performance we
will run a number of Pydrofoil variants. The first variant is simply Pydrofoil
with all optimizations turned on. Every further variant disables one more of the
optimizations I described in this post.

The variants are:

- pydrofoil-riscv-full: The Pydrofoil RISC-V emulator with all optimization
  turned on.
- pydrofoil-no-mem-immutability: Turns memory immutability tracking off.
- pydrofoil-no-jit: Additionally turns the JIT off and works only as an interpreter.
- pydrofoil-no-bv-int-opts: Additionally turns off the static optimizations that
  replace generic bitvector and generic integer operations with more specialize
  variants operating on machine word sizes.
- pydrofoil-no-spec: Additionally turns off inlining and function
  specialization.
- pydrofoil-no-static-opt: Additionally turns of all the remaining static
  optimizations.
- pydrofoil-no-runtime-smallint: Always uses `BigInteger` for Sail integers and
  doesn't dynamically check whether an integer would fit into a machine word.

In this post, I'm running only part of a single benchmark. Specifically, the
first 15 billion instructions of running deepsjeng from SPEC (which is a chess
engine going through the search tree of several chess positions), including
booting Linux to the point where it can start the benchmark. Obviously it's not
great to just stop the benchmark at a somewhat arbitrary point. However,
Pydrofoil runs the full benchmark in about five hours on my laptop and the
above Pydrofoil versions obviously become successively much slower, so it's
completely impractical to run any interesting benchmark to completion with them.

The results look like this:

![ablations](images/2025-pydrofoil-ablations.svg)

We can see that the JIT is the most important component for getting Pydrofoil's
performance, it provides (together with memory immutability tracking) a 15x
performance boost over not having it. The static bitvector and integer
optimizations are the most useful static optimizations that Pydrofoil does,
disabling them slows Pydrofoil down more than 4x; inlining, function
specialization and all other static optimizations are less important. Turning
the runtime-switchable integer representation off leads to a further 2x slow
down.

# Benchmarking QEMU, Spike, Pydrofoil and Sail

To also get an idea of how Pydrofoil fares against actually efficient emulators,
I'm running the full deepsjeng on top of QEMU, Pydrofoil, Spike, and Sail. The
latter two were fairly slow again, so I didn't run them to completion and
instead extrapolated their instructions/second numbers, the results should
therefore be taken with a grain of salt. In any case, here are the results:

![comparison qemu](images/2025-pydrofoil-qemu.svg)

Qemu is 14x faster than Pydrofoil, Sail is more than 200x slower than Pydrofoil,
Spike is more than 3x slower than Pydrofoil.


## Conclusion

Pydrofoil takes the Sail RISC-V model, which is written in a fairly high-level
specification language that is generic on bitvector widths. That Sail model is
then compiled to a much more efficient interpreter, using mostly well-known
static compilation techniques (including function specialization). Afterwards,
adding some runtime data structures that make the remaining cases of generic
integer types less inefficient helps lessen the impact of functions where static
optimizations aren't possible.

Using the RPython tracing JIT to make the emulator perform dynamic binary
translation improves the performance even more, particularly after making it
possible for the JIT to assume that the parts of RAM that store instructions are
mostly constant.

Perhaps not surprisingly, QEMU (a hand-written emulators that does DBT) still
has much better performance. Spike, which is also hand-written but is an
interpreter, gives less performance.
