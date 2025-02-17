<!--
.. title: Low Overhead Allocation Sampling in a Garbage Collected Virtual Machine
.. slug: pypy-gc-sampling
.. date: 2025-01-26 14:38:00 UTC
.. tags: gc, profiling, vmprof
.. category:
.. link:
.. description:
.. type: text
.. author: Christoph Jung
-->

## Introduction

There are many time-based statistical profilers around (like VMProf or py-spy
just to name a few). They allow the user to pick a trade-off between profiling
precision and runtime overhead. On the other hand there are memory profilers,
which profile every allocation, resulting in precise profiling, but larger
overhead (e.g. memray). In this post we describe our experimental approach to
low overhead statistical memory profiling tightly integrated into VMProf and
the PyPy Garbage Collector. The main technical insight is that the check,
whether an allocation should be sampled, can be folded into the bump pointer
allocator checks, PyPy’s GC uses to find out if it should start a minor
collection. This makes the fast path with and without memory sampling the same.
A tool like this can be handy for discovering functions, allocating lots of
memory, leading to longer GC pauses caused by collections.

## Background

To get an insight how the profiler and GC interact, lets take a brief look at
both of them first.

### VMProf

[VMProf](https://github.com/vmprof/vmprof-python) is a statistical time-based
profiler for PyPy. This means, VMProf samples the stack a certain
user-configured number of times per second. By adjusting this number, the
overhead of profiling can be modified to pick the correct trade-off between
overhead and precision of the profile. Additionally, VMProf has the ability to
record JIT traces, giving an insight what the JIT does to the executed
functions of the program. In the resulting profile, functions with huge runtime
stand out the most, functions with shorter runtime less so. If you want to get
a little more introduction to VMProf and how to use it with PyPy, you may look
at [this blog
post](https://pypy.org/posts/2024/05/vmprof-firefox-converter.html)

### PyPy’s GC

PyPy uses a generational incremental copying collector. That means there are
two spaces for allocated objects, the nursery and the old-space. Freshly
allocated objects will be allocated into the nursery. When the nursery is full
at some point, it will be collected and all objects that survive will be
tenured i.e. moved into the old-space. The old-space is much larger than the
nursery and is collected less frequent and incrementally (not completely
collected in one go, but step-by-step).

This is still a quite simplified explanation of PyPy’s GC, but we don't want to
go over every detail right now. Instead, we will take a look at the fast path
(allocations in the nursery) and how the nursery is collected.

### Bump Pointer Allocation in the Nursery

The nursery (a small continuous memory area) utilizes pointers, to keep track
from where on the nursery is free and where it ends, called `nursery_free` and
`nursery_top`. When memory is allocated, the GC checks if there is enough space
in the nursery left. If there is enough space, the `nursery_free` pointer will
be returned as the start address for the new allocated memory, and
`nursery_free` will be moved forward by the amount of allocated memory.


<img src="../../../images/2025_02_allocation_sampling_images/nursery_allocation.svg">


``` Python
def allocate(totalsize):
  # Save position, where the object will be allocated to as result
  result = gc.nursery_free
  # Move nursery_free pointer forward by totalsize
  gc.nursery_free = result + totalsize
  # Check if this allocation would exceed the nursery
  if gc.nursery_free > gc.nursery_top:
      # If it does => collect the nursery and allocate afterwards
      result = collect_and_reserve(totalsize)
  # result is a pointer into the nursery, obj will be allocated there
  return result
```

Understanding this is crucial for our allocation sampling approach, so let us
go through this step-by-step.

We already saw an example on how an allocation into a non-full nursery will
look like. But what happens, if the nursery is (too) full?

<img src="../../../images/2025_02_allocation_sampling_images/nursery_full.svg">


As soon as an object doesn't fit into the nursery anymore, it will be
collected. A nursery collection will move all surviving objects into the
old-space, so that the nursery is free afterwards, and the requested allocation
can be made.


<img src="../../../images/2025_02_allocation_sampling_images/nursery_collected.svg">


Note that this is still a bit of a simplification.

## Sampling Approach

To decide whether the GC should trigger a sample, the sampling logic is
integrated into the bump pointer allocation logic. Usually, when there is not
enough space in the nursery left to fulfill an allocation request, the nursery
will be collected and the allocation will be done afterwards. We re-use that
mechanism for sampling, by introducing a new pointer called `sample_point` that
is calculated by `sample_point = nursery_free + sample_n_bytes` where
`sample_n_bytes` is the number of bytes allocated before a sample is made (i.e.
our sampling rate).

Image we'd have a nursery of 2MB and want to sample every 512KB allocated, then
you could imagine our nursery looking like that:

<img src="../../../images/2025_02_allocation_sampling_images/nursery_sampling.svg">

And now here comes our secret trick. We use the sample point as `nursery_top`,
so that allocating a chunk of 512KB would exceed the nursery top and start a
nursery collection. But of course we don't want to do a minor collection just
then, so before starting a collection, we need to check if the nursery is
actually full or if that is just an exceeded sample point. The latter will then
trigger a sample via VMProf's C-interface.

Now I got to tell you, that the last picture is only a half-truth. There do not
exist more than one sample point at any time. After we created the sampling
point, it will be used as nursery top, if exceeded at some point, we will just
add `sample_n_bytes` to that sampling point, i.e. move it forward.

Here's how the updated `collect_and_reserve` function looks like:

``` Python
def collect_and_reserve(size_of_allocation):
    # Check if we exceeded a sample point or if we need to do a minor collection
    if gc.nursery_top == gc.sample_point:
        # One allocation could exceed multiple sample points
        # Sample, move sample_point forward
        while gc.sample_point < gc.nursery_free + size_of_allocation:
            vmprof.sample_now()
            gc.sample_point += sample_n_bytes
            
        # Set sample point as new nursery_top if it fits into the nursery
        if sample_point <= gc.real_nursery_top:
          gc.nursery_top = sample_point
        # Or use the real nursery top if it does not fit
        else:
          gc.nursery_top = gc.real_nursery_top

        # Is there enough memory left inside the nursery
        if gc.nursery_free + size_of_allocation <= gc.nursery_top:
          # Yes => move nursery_free forward
          gc.nursery_free += size_of_allocation
          return gc.nursery_free  
    
    # We did not exceed a sampling point and must do a minor collection, or
    # we exceeded a sample point but we needed to do a minor collection anways
    minor_collection()
    return gc.nursery_free 
```

## Why is the Overhead ‘low’

The tight integration of sampling into the nursery's bump-pointer logic does
add only slight overhead.

Every time an allocation exceeds the `sample_point`, `collect_and_reserve` is
called to sample over the size of the allocation (as described in previous
section). The resulting overhead is directly controlled by the sampling rate,
as the amount of samples is `size_of_allocation / sample_n_bytes`.

After sampling, the `sample_point` and `nursery_top` must be set accordingly.
This will be done once after sampling in `collect_and_reserve`.

Setting a pointer like `sampling_point`, `nursery_top`, etc. due to sampling,
are additions, subtractions, loads and stores on the lowest level. Those are
not expensive on their own, but rather when excecuted very often.

At some point a nursery collection will free the nursery and set the new
`sample_point` afterwards. 

The total number of times sampling overhead is introduced is:
- Some pointer arithmetic and a call to VMProf's c-interface every time the
  `sample_point` is exceeded
- Some pointer arithmetic after a nursery collection
- Some pointer arithmetic when enabling or disabling sampling (but that is of
  course constant overhead)

That means that the overhead mostly depends on the sampling rate and the amount
of memory allocated by the user program, as the combination of those two
factors determines the amount of samples.

Since the sampling rate can be adjusted from as low as 64 Byte to a theoretical
maximum of ~4 GB (at the moment), the tradeoff between number of samples (i.e.
profiling precision) and overhead can be completely adjusted.

We also suspect linkage between user program stack depth and overhead (a deeper
stack takes longer to walk, leading to higher overhead), especially when
walking the C call stack to.

## Sampling rates bigger than the nursery size

The nursery usually has a size of a few megabytes, but profiling long-running
or larger applications with tons of allocations could result in very high
number of samples per second (and thus overhead). To combat that it is possible
to use sampling rates higher than the nursery size.

The sampling point is not limited by the nursery size, but if it is 'outside'
the nursery (e.g. because `sample_n_bytes` is set to twice the nursery size) it
won't be used as `nursery_top` until it 'fits' into the nursery.


<img src="/images/2025_02_allocation_sampling_images/nursery_sampling_larger_than_nursery.svg">


After every nursery collection, we'd usually set the `sample_point` to
`nursery_free + sample_n_bytes`, but if it is larger than the nursery, then the
amount of collected memory during the last nursery collection is subtracted
from `sample_point`.


<img src="/images/2025_02_allocation_sampling_images/nursery_sampling_larger_than_nursery_post_minor.svg">


At some point the `sample_point` will be smaller than the nursery size, then it
will be used as `nursery_top` again to trigger a sample when exceeded.


## Differences to Time-Based Sampling

As mentioned in the introduction, time-based sampling ‘hits’ functions with
high runtime, and allocation-sampling ‘hits’ functions allocating much memory.
But are those always different functions? The answer is: sometimes. There can
be functions allocating lots of memory, that do not have a (relative) high
runtime.

Another difference to time-based sampling is that the profiling overhead does
not solely depend on the sampling rate (if we exclude a potential stack-depth -
overhead correlation for now) but also on the amount of memory the user code
allocates.

Let us look at an example:

If we’d sample every 1024 Byte and some program A allocates 3 MB and runs for 5
seconds, and program B allocates 6 MB but also runs for 5 seconds, there will
be ~3000 samples when profiling A, but ~6000 samples when profiling B. That
means we cannot give a ‘standard’ sampling rate like time-based profilers use
to do (e.g. vmprof uses ~1000 samples/s for time sampling), as the number of
resulting samples, and thus overhead, depends on sampling rate and amount of
memory allocated by the program.

For testing and benchmarking, we usually started with a sampling rate of 128Kb
and then halved or doubled that (multiple times) depending on sample counts,
our need for precision (and size of the profile).

## Evaluation

### Overhead

To investigate the overhead of allocation sampling, we ran some benchmarks.

But let us take a look at the allocation sampling overhead, by profiling some
benchmarks. Every benchmark ran 5 times with a sampling rate of `128Kb`.

The y-axis shows the overhead, while the x-axis indicates the equivalent of
samples per second. The overhead is computed as `runtime_with_sampling /
runtime_without_sampling` and the ammount of samples per second is computed by
`number_of_samples / runtime_in_seconds`.

All benchmarks ran with JIT and native profiling.

<img src="../../../images/2025_02_allocation_sampling_images/allocation_sampling_overhead.png">


As you may notice, the amounts of samples per second are quite different, and
the overhead does not scale linearly with the number of samples per second.

Let us compare that to ‘vanilla’ time sampling.

Again we ran those benchmarks with a series of time sampling rates. That is
1000, 5000, 10000, 15000, 20000, 25000 and 30000 samples per second.

[IMG time based sampling]

...

The benchmarks used are:

micro benchmark <link or code?>

gcbench https://github.com/pypy/pypy/blob/main/rpython/translator/goal/gcbench.py
- print statements removed

pypy translate step
- first step (annotation) of the pypy translation
- pypy path/to/rpython --opt=0 --cc=gcc --dont-write-c-files --gc=incminimark --annotate path/to/pypy/goal/targetpypystandalone.py

interpreter pystone
- pystone benchmark on top of an interpreted pypy on top of a translated pypy
- pypy path/to/pypy/bin/pyinteractive.py -c "import test.pystone; test.pystone.main(1)"

All benchmarks executed on:

Kubuntu 24.04
AMD Ryzen 7 5700U
24gb DDR4 3200MHz (dual channel)
SSD benchmarking at read: 1965 MB/s, write: 227 MB/s
- Sequential 1MB 1 Thread 8 Queues

Self built PyPy with allocation sampling features
- https://github.com/Cskorpion/pypy/tree/gc_allocation_sampling2.7

Modified VMProf with allocation sampling support
- https://github.com/Cskorpion/vmprof-python/tree/pypy_gc_allocation_sampling

### Case Study



## Future Work

There are multiple points we’d like to address in the future.

One very important thing when it comes to profiling is the overhead. One idea
on how to decrease the overhead per sample is, to not walk the entire stack
every time, but mark walked stack frames, so that for the next sample, we only
need to walk up to an already marked stackframe. This could reduce the
overhead, if the stacks do not change completely from sample to sample and
there is indeed a significant correlation between stack depth and overhead.

PyPy has a logging interface, which is used to log GC and JIT events with a
timestamp. Unfortunately those timestamps are the clock counts read from the
CPU’s `TSC` (Time Stamp Counter ~ number of cycles since last reset) register
(at least on x86/x86_64), which are not really suitable for measuring time.
VMProf on the other hand (our modified VMProf) uses timestamps retrieved with
unix’ `CLOCK_MONOTONIC`. This means we cannot exactly associate pypylog events
with VMProf samples. An easy fix would be to use the same timestamps for
pypylog as we do for vmprof, but this could introduce more overhead. A better
way of associating them, could be to record the `TSC` with each sample so we’d
get an approximate alignment of logged events and samples.

Another Idea would be extracting information about allocations from the GC,
e.g. type of object to be allocated, object size or even some statistics about
lifetime (if possible). For example PyPy could also log jitted functions, so we
can see what function got jitted at what time. Together with the sampled
statistics we’d have a good overview about what is happening with our code:
What functions have long runtime or huge memory usage, what functions got
jitted and (somewhat) how are allocations represented and handled inside the
gc. So you could see àllocation sampling as a first step towards a more
powerfull profiling suite.

The very last thing to append to our ‘future work’ list, are syscalls. Using
ptrace to trace syscalls could give an insight on where/when/how much your code
spent time opening files, reading from files, waiting for subprocesses to
finish, etc.
