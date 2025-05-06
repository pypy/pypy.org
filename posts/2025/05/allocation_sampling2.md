<!--
.. title: Profiling Types and Survival Rates in PyPy's Memory Profiler
.. slug: type-survival-profiling
.. date: 2025-04-14 9:57:00 UTC
.. tags: gc, profiling, vmprof
.. category:
.. link:
.. description:
.. type: text
.. author: Christoph Jung
-->

## Introduction

Not long ago, we wrote a [blogpost](https://pypy.org/posts/2025/02/pypy-gc-sampling.html) describing our approach to low overhead allocation sampling for PyPy.
In this post we want to discuss extending the allocation sampling profiler to also store two extra pieces of information for every allocation sample:

- the (RPython-level) type of the allocated object
- whether the object lived for a long time, or died relatively quickly

We also want to store some general statistics about the memory use of the PyPy GC.

Additionally, we want to elaborate on how we tested the interaction of those
features with the GC logic. Finally, we discuss the overhead of those features
and provide a case study to demonstrate how allocation sampling can be used.

## Getting more information from PyPy's GC

First, let us talk about the technical details. Hopefully you still remember
how nursery allocations and sampling worked, as described in the previous
blog post. Now we want to extend that approach by also finding out what type of
allocation (i.e., object) triggered a sample and, if it survived the next
minor collection. So let us directly dive into how PyPy's GC stores the type of
an object, by looking at an example depiction of how an object with metadata looks like.

<img src="/images/2025_05_allocation_sampling_images_2/object.png">

Every object allocated by the GC has a header, composed of a 16-bit type ID and
16 bits for GC flags.
This means for every object allocated, as soon as we've got its address, we can
just read the type from its header. Unfortunately, those type IDs correspond to
RPython types and not Python (app-level) types. The RPython-level types may not
be very intuitive for non PyPy developers. Unfortunately getting the type at
the Python level would either be computationally costly or even impossible, due
to the objects not being completely initialized at the point where the GC would
like to find out the type.

Let's talk about the second piece of information we want to get our hands on:
Did an allocated object survive the next minor collection after it was
allocated, or did it not? During minor collections, there is a point in time
where surviving objects are known and marked via one GC header flag. This is
only a rough indication of how long the object survived, but since most objects
die young (i.e. before the first minor collection), it's still interesting to
identify call sites where object get allocated that survive longer than one
minor collection.

A quick recap of how sampling worked: Every `n` bytes allocated, a sample will
be triggered. Afterwards, the allocation request will be fulfilled, returning
the address of free memory for the newly allocated object to the caller. That
is where our new modifications start. Before returning the address of that
freshly allocated object, we put that address into a list. In this way, we
maintain a list `sampled_objects` of the sampled objects that were allocated
since that last collection.

This list is then used during the next minor collection. After the heap has
been traced and all surviving objects are known, we can take every address
inside `sampled_objects` and look into the corresponding GC header to read the
type ID and to find out whether the object survived or not. These two pieces of
information are then stored into the profile on disk, together with some
statistics about the current state of the GC.

That information is the following:
The `total_size_of_arenas` tells us how much space the GC actually has to
allocate tenured objects, while `total_memory_used` tells us how much of that
is already occupied. But there is more to a VM than just the memory the GC
manages, thus the `vmRSS` tells us how much memory PyPy consumes from the point
of view of the operating system.
Finally, the `GC state` tells the current major collection phase, which is one
of: `scanning, marking, sweeping, finalizing`.

To be able to map type IDs of RPython types from numbers to something human-readable,
we also dump a mapping of RPython type IDs to their respective names into the profile so that an UI tool like the
[vmprof-firefox-converter](https://github.com/Cskorpion/vmprof-firefox-converter)
may use that to display the actual type names. As said earlier, those RPython
names may not be super useful for non PyPy developers, so we plan to add
descriptions for most common RPython types to the vmprof-firefox-converter. 


## Evaluation

### Verification

After talking about how it works, we now have to talk about how we can verify
the correctness of the extracted information.

Of course, the first thing we did was write some unit tests, but a few unit
tests don't really guarantee the correctness of the complex interaction of the
GC- and allocation sampling logic.

Secondly, we implemented allocation sampling into the already existing
[randomized testing facility (fuzzer)](https://pypy.org/posts/2024/03/fixing-bug-incremental-gc.html) for PyPy's GC.

Fuzzing PyPy's GC with hypothesis has two phases. The first phase is generating
random action sequences. Those actions consist of object-, string-, or array
allocations, freeing allocated objects, accessing an object and from now on
also activating and deactivating allocation sampling with a random sampling
rate. In the second phase, these actions are executed against the GC
implementation and their intermediate results asserted.

If there is a bug in the GC, e.g., freeing an object too early, the fuzzer
could produce a random action sequence that leads to an error when accessing an
already freed object.

When generating these actions, we also keep track of how much memory will be
allocated when they are executed. With this information, we can decide if each
generated allocation action will trigger a sample. When these actions are
executed in the second phase, we can check for each allocation if it should
trigger a sample and if it actually did. For a failing check we then get the
sequence of actions that led to the failed check, so we can trace the bug down.

Fuzzing was very helpful for getting rid of many bugs inside the allocation
sampling logic, because it demonstrated interactions between sampling and
garbage collection that we hadn't foreseen properly.

### Overhead

We already talked about that last time, but adding now features could add more
overhead, so we re-ran the benchmarks from the last post. We won't go into
further details about that here, but it turns out that the new features of also
persisting RPython types and whether the object survived the next minor
collection did not change the overhead of sampling in a measurable way. The
reason for that is that the main cost of allocation sampling is the cost of
walking the call stack at the allocation point.

Every time we sample, we also store the address of the allocated object in a
list. That list, together with some GC stats, is then dumped to VMProf at every
minor collection. This only introduces little overhead when sampling is
enabled, and only one new pointer comparison at every minor collection when
sampling is turned off.


## Case Study

Here we want to show you a real world example of how we used allocation
sampling with the vmprof-firefox-converter to profile some real-world program
and learned something from that.

### PyPy VM Optimization

One day we profiled some benchmark executing SymPy functions and looked at
sampled list allocations.

<img src="/images/2025_05_allocation_sampling_images_2/pure_from_args_calltree.png">

There we stumbled upon PyPy's JIT-optimizer functions `postprocess_INT_ADD` and
`pure_from_args`. Both those functions take part in marking an (integer-?)
operation as pure.

If PyPy's JIT encounters a `INT_ADD` operation that is pure and thus can be
cached and replaced by its result, `postprocess_INT_ADD` will be called to also
mark `INT_SUB` operations on the corresponding arguments as pure. 

This is done by getting the arguments `arg0` and `arg1` of the `INT_ADD` and
then calling `pure_from_args(INT_SUB, [arg0, arg1])` (simplified) which caches
`INT_SUB` for the current arguments.

Post-Processing optimization is done not only for `INT_ADD` but `INT_MUL`,
`INT_XOR` and others too, BUT there are never more than two arguments passed to
`pure_from_args` inside that list.

`pure_from_args` looks (somewhat simplified) like that:

``` python
def pure_from_args(op, args_list): 
    rop = ResOperation(op, [get_box_replacement(arg) for arg in args_list])
    ...
```

Knowing that `pure_from_args` is only ever called with up to two arguments
inside that list, it could be split up into two functions, one for the
one-argument case and one for the two-argument case:

(Also a bit simplified)

``` python  
def pure_from_args1(abstract_op, arg0): 
    rop = ResOperation(op)
    rop.setarg(0, get_box_replacement(arg0))
    ...

def pure_from_args2(abstract_op, arg0, arg1):
    rop = ResOperation(op)
    rop.setarg(0, get_box_replacement(arg0))
    rop.setarg(1, get_box_replacement(arg1))
    ...
```

Now `arg0` and `arg1` can be passed directly to
`pure_from_args1/pure_from_args2` and don't need to be put into a list.
Additionally they don't need to be repacked into a list to be passed to
`ResOperation`.

Then all call sites were
[adapted](https://github.com/pypy/pypy/commit/ef590f639e529ebe319c7d5ff8f5e03e31bcc304)
to either call `pure_from_args1` or `pure_from_args2` directly, and thus saving
two list allocations per `pure_From_args` call.


## Summary
 
In this and the previous blog post, we introduced and explained the technical
details of allocation sampling in PyPy's GC with VMProf. Using this tool to
simultaneously do allocation and time sampling can give insight into where the
program spends time and what functions allocate much memory, leading to garbage
collections. This tool is aimed at both PyPy developers and non-PyPy
developers, with the target of being easy to use while introducing little
overhead. 

## Future Work 

We have a bunch of ideas for features that could be added to VMProf in the
future.

One very important thing when it comes to profiling is the overhead. One idea
on how to reduce the overhead per sample is, to not walk the entire stack every
time but mark walked stack frames so that for the next sample, we only need to
walk up to an already marked stack frame. This could reduce the overhead if the
stacks do not change completely from sample to sample and there is indeed a
significant correlation between stack depth and overhead. 
 
PyPy has a logging interface, which is used to log GC and JIT events with a
timestamp. Unfortunately those timestamps are the clock counts read from the
CPU’s `TSC` (Time Stamp Counter ~ number of cycles since last reset) register
(at least on x86/x86_64), which are not perfectly suitable for measuring time.
VMProf on the other hand (our modified VMProf) uses timestamps retrieved with
Unix' `CLOCK_MONOTONIC`. This means we cannot exactly associate pypylog events
with VMProf samples. An easy fix would be to use the same timestamps for
pypylog as we do for VMProf, but this could introduce more overhead. A better
way of associating them, could be to record the `TSC` with each sample so we’d
get an approximate alignment of logged events and samples. 

The very last thing to append to our ‘future work’ list are syscalls. Using
ptrace to trace syscalls could give an insight on where/when/how much your code
spent time opening files, reading from files, waiting for subprocesses to
finish, etc. 

We are also hoping to transfer some of the techniques used here for profiling
PyPy to profile the ISA simulator generator Pydrofoil.

-- Christoph Jung and CF Bolz-Tereick
