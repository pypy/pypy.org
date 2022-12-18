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
RPython meta-tracing JIT infrastructure. This project is called "Pydrofoil",
and it aims at automatically generating a fast emulator for the RISC-V
architecture from a formal specification of the behaviour of that architecture.
The project is joint work with John Witulski, Martin Berger, Matti Picus. We
have received some sponsorship from RISC-V International, for which we are
immensely grateful!

In this post I'll describe how to use Pydrofoil, show some early benchmark
results and describe the motivation and architecture of the project.



What are Sail and the Sail RISC-V model?
========================================

The `Sail language`__ is a domain-specific language developed at the University
of Cambridge. The goal of the language is to be able to specify the semantics of
instruction set architectures in a very precise way, to be able to formally
reason about the behaviour of machine code programs. 

The language is a statically typed functional language with pattern matching and
some support for liquid types. It contains a number of datatypes that are
particularly suited for the task of describing the behaviour ISAs, such as
bitvectors, arbitrary-width integers, real numbers.

A number of ISAs have been specified in this language, but we'll only talk about
the one for RISC-V in this post. The Sail ISA specification for RISC-V is
interesting because it is supposed to be considered the "Golden Model" for
RISC-V, meaning it is the ground truth of how the architecture is supposed to
behave.

Let's look at some example code from the RISC-V Sail model.

...


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
relatively slow and only emulates between about 1000-10000 instructions per
second, which is really not too great considering that hand-written emulators
like Spike or QEMU can sometimes run up to 100 Million instructions per second.

This slow emulation speed can be a problem when trying to test somewhat complex
software in emulation, e.g. booting the Linux kernel takes over an hour on the
Sail-RISC-V emulator.

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
way than the existing. Instead of generating C code, Pydrofoil takes a Sail
model and produces RPython code. In many ways, the ideas of the RPython project
and the Sail projects overlap. Sail is a language to describe the semantics of
an ISA in a high-level way. Sail provides a lot of common infrastructure, such
as libraries, support for formal proofs and a way to generate an emulator.
RPython on the other hand is a language to describe semantics of dynamic
languages in a high-level way. RPython provides common infrastructure, such as a
reasonably good garbage collector and a reusable just-in-time compiler.
Therefore combining the two projects in many ways felt natural.

Pydrofoil generates RPython code by parsing Sail's JIB representation, which are
an intermediate language that the Sail compiler uses to represent the input
programs. At this stage, the Sail programs have already been parsed,
type-checked and optimized by the Sail compiler, therefore Pydrofoil doesn't
have to do these tasks. Pydrofoil parses the JIB files, does some minor
transformations and then produces RPython code from them.

This RPython code is then combined with some support code that is hand-written
in RPython. Most of that support code can be shared between different ISAs, some
needed to be hand-written for RISC-V.



The idea for why this could give better speedups is the following:

- The first reason is RPython's tracing JIT. The hope would be that it can be
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

- how to use it
  - download release or build yourself
  - booting linux

Some early benchmark results
===========================================================


Conclusion
===========================================================

- risc-v international support
