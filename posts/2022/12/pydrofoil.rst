.. title: Pydrofoil: Fast jitting RISC-V emulators with the PyPy JIT
.. slug: pydrofoil-riscv-emulators
.. date: 2022-12-23 18:00:00 UTC
.. tags: jit, riscv, sail
.. category:
.. link:
.. description:
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

Since June or so, I have been working on a new prototype project that uses the
RPython meta-tracing JIT infrastructure to simulate a CPU instruction set. This
project is called Pydrofoil_,
and it aims at automatically generating a fast emulator for the RISC-V
architecture from a formal specification of the behaviour of that architecture.
The project is joint work with John Witulski, Martin Berger, Matti Picus. We
have received some sponsorship from RISC-V International, for which we are
immensely grateful!

In this post I'll describe how to use Pydrofoil, show some early benchmark
results and describe the motivation and architecture of the project.


What are Sail and the Sail RISC-V model?
========================================

The `Sail language`_ is a domain-specific language developed at the University
of Cambridge. The goal of the language is to be able to specify the semantics of
instruction set architectures (ISAs) in a very precise way, to be able to formally
reason about the behaviour of machine code programs. 

The language is a statically typed functional language with pattern matching and
some support for liquid types. It contains a number of datatypes that are
particularly suited for the task of describing the behaviour of ISAs, such as
bitvectors, arbitrary-width integers, real numbers.

A number of ISAs have been specified in this language, but we'll only talk about
the one for RISC-V (Sail-RISCV_) in this post. The Sail ISA specification for
RISC-V is interesting because it is supposed to be considered the "Golden
Model" for RISC-V, meaning it is the ground truth of how the architecture is
supposed to behave.

We'll now go through an example of the Sail code for the ITYPE `RISCV
instruction`_. ITYPE instructions are arithmetic integer instructions with an
immediate value.

The first part of the Sail model is an "AST" declaration, which shows the
information that is encoded in such an instruction::

    /* the assembly abstract syntax tree (AST) clause for the ITYPE instructions */

    union clause ast = ITYPE : (bits(12), regbits, regbits, iop)

The ``bits(12)`` type is a bitvector of 12 bits, storing the immediate.
``regbits`` is declared elsewhere to be ``bits(5)``, the two ``regbits``
components are for the source and the destination register. ``iop`` is an
enumeration that lists the various ``ITYPE`` instruction cases::

    enum iop = {RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU,
                RISCV_XORI, RISCV_ORI, RISCV_ANDI}    /* immediate ops */

The following function describes a mapping between that ``iop`` enum and the
bits used in the instruction encoding. This is a bidirectional function (it uses
``<->``), it can be used to both turn the instruction bits into the enum (when
decoding an instruction), but also the other way around::

    /* the encode/decode mapping between AST elements and 32-bit words */

    mapping encdec_iop : iop <-> bits(3) = {
      RISCV_ADDI  <-> 0b000,
      RISCV_SLTI  <-> 0b010,
      RISCV_SLTIU <-> 0b011,
      RISCV_ANDI  <-> 0b111,
      RISCV_ORI   <-> 0b110,
      RISCV_XORI  <-> 0b100
    }

And here comes the actual decoding of ``ITYPE`` instructions. It describes how
the instruction bits are combined to form an ``ITYPE``, and how those parts
relate to the information in the ``ITYPE`` AST::

    mapping clause encdec = ITYPE(imm, rs1, rd, op) <-> imm @ rs1 @ encdec_iop(op) @ rd @ 0b0010011

Here the ``@`` operator is bitvector concatenation. ``encdec`` is again a
bidirectional function, so it can be used to decode an instruction, but also to
take an AST and turn it into one.

The next function defines the actual execution semantics of the instructions::

    /* the execution semantics for the ITYPE instructions */

    function clause execute (ITYPE (imm, rs1, rd, op)) = {
      let rs1_val = X(rs1);
      let immext : xlenbits = EXTS(imm);
      let result : xlenbits = match op {
        RISCV_ADDI  => rs1_val + immext,
        RISCV_SLTI  => EXTZ(rs1_val <_s immext),
        RISCV_SLTIU => EXTZ(rs1_val <_u immext),
        RISCV_ANDI  => rs1_val & immext,
        RISCV_ORI   => rs1_val | immext,
        RISCV_XORI  => rs1_val ^ immext
      };
      X(rd) = result;
      true
    }

The code reads the value of source register ``rs1``, then sign-extends the
immediate to ``xlenbits`` (which could be 32, 64 or 128 bits) using the ``EXTS``
function. Then it pattern-matches on the ``op`` to compute ``result``. That
resulting value is then stored into the destination register ``rd``.


Turning the Sail RISC-V ISA model into an emulator
===========================================================

One of the features of the Sail DSL is that it can take an ISA specification and
turn it into an emulator for that ISA. To do this, it compiles the Sail code
into C, adds a bit of hand-written C support and glue code and uses a C compiler
to produce a binary.

The Sail-RISC-V emulator produced in this way can execute the RISC-V test suite
which checks that the instructions are implemented correctly. It is also
complete enough to boot Linux up to a login prompt.

However, one downside of the emulator generated this way is that it is
relatively slow and only emulates between about 1000-10,000 instructions per
second, which is really not too great considering that hand-written emulators
like Spike or QEMU can sometimes run hundreds of millions instructions per second.

This slow emulation speed can be a problem when trying to test somewhat complex
software in emulation, e.g. booting the Linux kernel takes over an hour on the
Sail-RISC-V emulator.

.. comment_::
  The Sail-RISCV website claims "This enables one to boot Linux in about 4
  minutes, and FreeBSD in about 2 minutes. Memory usage for the C emulator when
  booting Linux is approximately 140MB. That is very different from "over an
  hour"

Performance problems of the Sail RISC-V model
===========================================================

When I started this project I was trying to understand why the Sail-RISC-V
generator was so slow. The Sail compiler tries to infer the bitwidth all the
bitvectors and integers that the model operates on. For those bitvectors and
integers that have a proven-to-be-finite width that is below 64bits, the
generated C code represents them as a C integer type. However, for the remaining
bitvectors and integers the Sail compiler represents them using the
arbitrarily-sized integer implementation of the GMP library. In particular, this
means that all operations on such integers/bitvectors has to allocate the result
on the heap, and deallocate them if they aren't being used any more.

Some profiling bit revealed that the Sail-RISC-V emulator spends most of its
time calling ``malloc`` and ``free`` on this GMP integers.


Pydrofoil's Architecture
===========================================================

The idea of Pydrofoil is to generate emulators from a Sail model in a different
way. Instead of generating C code, Pydrofoil takes a Sail
model and produces RPython code. In many ways, the ideas of the RPython project
and the Sail projects overlap. Sail is a language to describe the semantics of
an ISA in a high-level way. Sail provides a lot of common infrastructure, such
as libraries, support for formal proofs and a way to generate an emulator.
RPython on the other hand is a language to describe semantics of dynamic
languages in a high-level way. RPython provides common infrastructure, such as a
reasonably good garbage collector and a reusable just-in-time compiler.
Therefore combining the two projects in many ways felt natural.

Pydrofoil generates RPython code by parsing Sail's JIB representation:
an intermediate language that the Sail compiler uses to represent the input
programs. When producing JIB, the Sail programs have already been parsed,
type-checked and optimized by the Sail compiler, therefore Pydrofoil doesn't
have to do these tasks. Pydrofoil parses the JIB files, does some minor
transformations and then produces RPython code from them.

This RPython code is then combined with some support code that is hand-written
in RPython. Most of that support code can be shared between different ISAs, some
needed to be hand-written for RISC-V.

The speedups come from the following:

- The first reason is RPython's tracing JIT. It can be
  used to perform dynamic binary translation from the guest RISC-V instructions
  that are running on top of the generated emulator, to host machine code, at
  runtime.

- The second reason has to do with bitvector and integer representation. I'll
  describe this in the next section.


Integer and bitvector representation in Pydrofoil
===========================================================

- integers and bitvectors
  - dynamic typing

Downloading Pydrofoil and booting Linux on it
===========================================================

We offer pre-built ``pydrofoil-riscv`` emulators at ``link``. These are built
according to the `build documentation`_ and are available for ``x86_64`` linux
and macOS. These can be use as follows to boot linux from the `Sail-RISCV`_
repo::

    dtc < os-boot/rv64-64mb.dts > os-boot/rv64-64mb.dtb
    ./pydrofoil-riscv -b os-boot/rv64-64mb.dtb os-boot/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl -l 230000000

This command will run the Linux image that is part of the sail-riscv repo until
the login prompt. The ``dtb`` file is a device tree blob that describes the
emulated hardware to the operating system, it gets generated from a
human-readable input file with the ``dtc`` command.

Booting Linux takes a bit less than 4 minutes on Pydrofoil. You can try the
equivalent command on the standard Sail emulator::

    ./c_emulator/riscv_sim_RV64 -b os-boot/rv64-64mb.dtb os-boot/rv64-linux-4.15.0-gcc-7.2.0-64mb.bbl -l 230000000 -V

which takes roughly 75 minutes.

Some early benchmark results
===========================================================


Conclusion
===========================================================

- risc-v international support

.. _Pydrofoil: https://docs.pydrofoil.org
.. _`Sail language`: https://github.com/riscv/sail-riscv#what-is-sail
.. _`Sail-RISCV`: https://github.com/riscv/sail-riscv#riscv-sail-model
.. _`RISCV instruction`: https://github.com/riscv/sail-riscv#example-risc-v-instruction-specifications
.. _`build documentation`: https://docs.pydrofoil.org/en/latest/building_pydrofoil.html
