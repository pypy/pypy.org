<!--
.. title: Fixing a Bug in PyPy's Incremental GC
.. slug: fixing-bug-incremental-gc
.. date: 2024-03-26 19:14:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: Carl Friedrich Bolz-Tereick
-->

# Introduction

Since last summer, I've been looking on and off into a weird and hard to
reproduce [crash bug in PyPy](https://github.com/pypy/pypy/issues/3959). It was
manifesting only on CI, and it seemed to always happen in the AST rewriting
phase of [pytest](https://pytest.org), the symptoms being that PyPy would crash
with a segfault. All my attempts to reproduce it locally failed, and my
attempts to try to understand the problem by dumping the involved ASTs lead
nowhere.

A few weeks ago, we got [two more](https://github.com/PyO3/pyo3/issues/3766)
[bug reports](https://github.com/orgs/pypy/discussions/4923), the last one by
the authors of the [nanobind](https://nanobind.readthedocs.io/) binding
generator, with the same symptoms: crash in AST rewriting, only on CI. I
decided to make a more serious push to try to find the bug this time.
Ultimately the problem turned out to be several bugs in PyPy's garbage
collector (GC) that had been there since its inception in
[2013](https://www.pypy.org/posts/2013/10/incremental-garbage-collector-in-pypy-8956893523842234676.html).
Understanding the
situation turned out to be quite involved, additionally complicated by this
being the first time that I was working on this particular aspect of PyPy's GC.
Since the bug was so much work to find, I thought I'd write a blog post about
it.

The blog post consists of three parts: first a chronological description of
what I did to find the bug, a technical explanation of what goes wrong, some
reflections on the bug (and then a bonus bug I also found in the process).

# Finding the Bug

I started from the failing [nanobind CI
runs](https://github.com/wjakob/nanobind/actions/runs/8234561874/job/22516568891)
that ended with a segfault of the PyPy interpreter. This was only an
intermittent problem, not every run was failing. When I tried to just run the
test suite locally, I couldn't get it to fail. Therefore at first I tried to
learn more about what was happening by looking on the CI runners.

## Running on CI

I forked the nanobind repo and hacked the CI script in order to get it to use a
PyPy build with [full debug information and more assertions turned on](https://doc.pypy.org/en/latest/build.html#making-a-debug-build-of-pypy). In order
to increase the probability of seeing the crash I added an otherwise unused
[matrix](https://docs.github.com/en/actions/using-jobs/using-a-matrix-for-your-jobs)
variable to the CI script that just contained 32 parameters. This means every
build is done 32 times (sorry Github for wasting your CPUs 😕). With that
amount of repetition, I got at least one job of every build that was crashing.

Then I added the `-Xfaulthandler` option to the PyPy command which will use the
[faulthandler](https://docs.python.org/3.11/library/faulthandler.html) module
try to print a Python stacktrace if the VM segfaults to confirm that PyPy was
indeed crashing in the [AST](https://docs.python.org/3/library/ast.html)
[rewriting
phase](https://github.com/pytest-dev/pytest/blob/main/src/_pytest/assertion/rewrite.py)
of pytest, which pytest uses for [nicer
assertions](https://docs.pytest.org/en/7.1.x/how-to/assert.html#asserting-with-the-assert-statement).
I experimented with hacking our faulthandler implementation to also give me a
C-level callstack, but that didn't work as well as I hoped.

Then I tried to run [gdb](https://sourceware.org/gdb/) on CI to try to get it
to print a C callstack at the crash point. You can get gdb to execute commands
as if typed at the prompt with the `-ex` commandline option, I used something
like this:

```
gdb -ex "set confirm off" -ex "set pagination off" -ex \
    "set debuginfod enabled off" -ex run -ex where -ex quit \
    --args <command> <arguments>
```

But unfortunately the crash never occurred when running in gdb.

Afterwards I tried the next best thing, which was configuring the CI runner to
[dump a core file and upload it as a build
artifact](https://github.com/itamarst/gha-upload-cores), which worked. Looking
at the cores locally only sort of worked, because I am running a different
version of Ubuntu than the CI runners. So I used
[tmate](https://mxschmitt.github.io/action-tmate/) to be able to log into the
CI runner after a crash and interactively used gdb there. Unfortunately what I
learned from that was that the bug was some kind of **memory corruption**,
which is always incredibly unpleasant to debug. Basically the header word of a
Python object had been corrupted somehow at the point of the crash, which means
that it's [vtable](https://en.wikipedia.org/wiki/Virtual_method_table) wasn't
usable any more.

(Sidenote: [PyPy doesn't really use a vtable
pointer](https://www.pypy.org/posts/2009/10/gc-improvements-6174120095428192954.html#unifying-the-vtable-ptr-with-the-gc-header),
instead it uses half a word in the header for the vtable, and the other half
for flags that the GC needs to keep track of the state of the object.
Corrupting all this is still bad.)

## Reproducing Locally

At that point it was clear that I had to push to reproduce the problem on my
laptop, to allow me to work on the problem more directly and not to always have
to go via the CI runner. Memory corruption bugs often have a lot of randomness
(depending on which part of memory gets modified, things might crash or more
likely just happily keep running). Therefore I decided to try to brute-force
reproducing the crash by simply running the tests many many times. Since the
crash happened in the AST rewriting phase of pytest, and that happens only if
no [pyc
files](https://stackoverflow.com/questions/2998215/if-python-is-interpreted-what-are-pyc-files)
of the bytecode-compiled rewritten ASTs exist, I made sure to delete them
before every test run.

To repeat the test runs I used
[multitime](https://tratt.net/laurie/src/multitime/), which is a simple program
that runs a command repeatedly. It's meant for lightweight benchmarking
purposes, but it also halts the execution of the command if that command exits
with an error (and it sleeps a small random time between runs, which might help
with randomizing the situation, maybe). Here's a demo:

<script src="https://asciinema.org/a/648877.js" id="asciicast-648877" async="true"></script>

([Max](https://bernsteinbear.com/) pointed out
[autoclave](https://github.com/silentbicycle/autoclave) to me when reviewing
this post, which is a more dedicated tool for this job.)

Thankfully, running the tests repeatedly eventually lead to a crash, solving my
"only happens on CI" problem. I then tried various variants to exclude possible
sources of errors. The first source of errors to exclude in PyPy bugs is the
just-in-time compiler, so I reran the tests with `--jit off` to see whether I
could still get it to crash, and thankfully I eventually could (JIT bugs are
often very annoying).

Next source of bugs to exclude where C-extensions. Since those were the tests
of nanobind, a framework for creating C-extension modules I was a bit worried
that the bug might be in our emulation of CPython's C-API. But running PyPy
with the `-v` option (which will print all the imports as they happen)
confirmed that at the point of crash no C-extension had been imported yet.

## Using `rr`

I still couldn't get the bug to happen in GDB, so the tool I tried next was
[rr](https://rr-project.org/). rr can record the execution of a program and
later replay it arbitrarily often. This gives you a time-traveling debugger
that allows you to execute the program backwards in addition to forwards.
Eventually I managed to get the crash to happen when running the tests with `rr
record --chaos` (`--chaos` randomizes some decisions that rr takes, to try to
increase the chance of reproducing bugs).

Using rr well is quite hard, and I'm not very good at it. The main approach I
use with rr to debug memory corruption is to replay the crash, then set a
[watchpoint](https://sourceware.org/gdb/current/onlinedocs/gdb.html/Set-Watchpoints.html)
for the corrupted memory location, then use the command `reverse-continue` to
find the place in the code that mutated the memory location. `reverse-continue`
is like `continue`, except that it will execute the program backwards from the
current point. Here's a little demo of this:

<script src="https://asciinema.org/a/648814.js" id="asciicast-648814" async="true"></script>

Doing this for my bug revealed that the object that was being corrupted was
erroneously collected by the garbage collector. For some reason the GC had
wrongly decided that the object was no longer reachable and therefore put the
object into a freelist by writing a pointer to the next entry in the freelist
into the first word of the object, overwriting the object's header. The next
time the object was used things crashed.

## Side-quest: wrong GC assertions

At this point in the process, I got massively side-tracked. PyPy's GC has a
number of debug modes that you can optionally turn on. Those slow down the
program execution a lot, but they should in theory help to understand why the
GC goes wrong. When I turned them on, I was getting a failing assertion really
early in the test execution, complaining about an invariant violation in the GC
logic. At first this made me very happy. I thought that this would help me fix
the bug more quickly.

Extremely frustratingly, after two days of work I concluded that the assertion
logic itself was wrong. I have fixed that in the meantime too, the details
of that are in the bonus section at the end of the post.

## Using GDB scripting to find the real bug

After that disaster I went back to the earlier rr recording without GC assertions
and tried to understand in more detail why the GC decided to free an object
that was still being referenced. To be able to do that I used the [GDB Python
scripting
API](https://sourceware.org/gdb/current/onlinedocs/gdb.html/Python-API.html) to
write some helper commands to understand the state of the GC heap (rr is an
extension of GDB, so the GDB scripting API works in rr too).

The first (small) helper command I wrote with the GDB scripting API was a way
to pretty-print the currently active GC flags of a random PyPy object, starting
just from the pointer. The more complex command I wrote was an object tracer,
which follows pointers to GC objects starting from a root object to explore the
object graph. The object tracer isn't complete, it doesn't deal with all the
complexities of PyPy's GC. But it was good enough to help me with my problem, I
found out that the corrupted object was stored in an array.

As an example, here's a function that uses the GDB API to walk one of the
helper data structures of the GC, a stack of pointers:

```python
def walk_addr_stack(obj):
    """ walk an instance of the AddressStack class (which is a linked list of
    arrays of 1019 pointers).

    the first of the arrays is only partially filled with used_in_last_chunk
    items, all the other chunks are full."""
    if obj.type.code == gdb.TYPE_CODE_PTR:
        obj = obj.dereference()
    used_in_last_chunk = lookup(obj, "used_in_last_chunk")
    chunk = lookup(obj, "inst_chunk").dereference()
    while 1:
        items = lookup(chunk, "items")
        for i in range(used_in_last_chunk):
            yield items[i]
        chunk = lookup(chunk, "next")
        if not chunk:
            break
        chunk = chunk.dereference()
        used_in_last_chunk = 1019
```

The full file of supporting code I wrote can be found in [this
gist](https://gist.github.com/cfbolz/13cadcbbef321d93fc9790dff6f60a6a). This is
pretty rough throw-away code, however.

In the following recording I show a staged debugging session with some of the
extra commands I wrote with the Python API. The details aren't important, I
just wanted to give a bit of a flavor of what inspecting objects looks like:

<script src="https://asciinema.org/a/648889.js" id="asciicast-648889" async="true"></script>

The next step was to understand why the array content wasn't being correctly
traced by the GC, which I eventually managed with some [conditional
breakpoints](https://www.fayewilliams.com/2011/07/13/gdb-conditional-breakpoints/),
more watchpoints, and using `reverse-continue`. It turned out to be a bug that
occurs when the content of one array was memcopied into another array. The
technical details of why the array wasn't traced correctly are described in
detail in the next section.

## Writing a unit test

To try to make sure I really understood the bug correctly I then wrote a GC
unit test that shows the problem. Like most of PyPy, our GC is written in
RPython, a (somewhat strange) subset/dialect of Python2, which can be compiled
to C code. However, since it is also valid Python2 code, it can be [unit-tested
on top of a Python2
implementation](https://www.pypy.org/posts/2022/04/how-is-pypy-tested.html)
(which is one of the reasons why we keep maintaining PyPy2).

In the GC unit tests you have a lot of control about what order things happen
in, e.g. how objects are allocated, when garbage collection phases happen, etc.
After some trying I managed to write a test that crashes with the same kind of
memory corruption that my original crash exhibited: an object that is still
reachable via an array is collected by the GC. To give you a flavor of what
this kind of test looks like, here's an (edited for clarity) version of the
test I eventually managed to write

```python
def test_incrementality_bug_arraycopy(self):
	source = self.malloc(VAR, 8) # first array
	# the stackroots list emulates the C stack
	self.stackroots.append(source)
	target = self.malloc(VAR, 8) # second array
	self.stackroots.append(target)
	node = self.malloc(S) # unrelated object, will be collected
	node.x = 5
    # store reference into source array, calling the write barrier
	self.writearray(source, 0, node)
	val = self.gc.collect_step()
	source = self.stackroots[0] # reload arrays, they might have moved
	target = self.stackroots[1]
	# this GC step traces target
	val = self.gc.collect_step()

	# emulate what a memcopy of arrays does
	res = self.gc.writebarrier_before_copy(source, target, 0, 0, 2)
	assert res
	target[0] = source[0] # copy two elements of the arrays
	target[1] = source[1]
    # now overwrite the reference to node in source
	self.writearray(source, 0, lltype.nullptr(S))
	# this GC step traces source
	self.gc.collect_step()
	# some more collection steps, crucially target isn't traced again
	# but node is deleted
	for i in range(3):
		self.gc.collect_step()
	# used to crash, node got collected
	assert target[0].x == 5

```

One of the good properties of testing our GC that way is that all the memory is
emulated. The crash in the last line of the test isn't a segfault at all,
instead you get a nice exception saying that you tried to access a freed chunk
of memory and you can then debug this with a python2 debugger.

## Fixing the Bug

With the unit test in hand, fixing the test was relatively straightforward (the
diff in its simplest form is anyway only a [single line
change](https://github.com/pypy/pypy/commit/78bbeb93471b5f38438004e971f4b4f84ab17a84)).
After this first version of my fix, I
[talked to Armin
Rigo](https://github.com/pypy/pypy/issues/4925#issuecomment-2014459454) who
helped me find different case that was still wrong, in the same area of the
code.

I also got help by the developers at [PortaOne](https://portaone.com/)
who are using PyPy on their servers and had seen some [mysterious PyPy
crashes](https://github.com/pypy/pypy/issues/4900)
recently, that looked related to the GC. They did test deployments of my fixes
in their various stages to their servers to try to see whether stability
improved for them. Unfortunately in the end it turned out that their crashes
are an unrelated GC bug related to object pinning, which we haven't resolved
yet.


## Writing a GC fuzzer/property based test

Finding bugs in the GC is always extremely disconcerting, particularly since
this one manged to hide for so long (more than ten years!). Therefore I wanted
to use these bugs as motivation to try to find more problems in PyPy's GC. Given
the ridiculous effectiveness of fuzzing, I used
[hypothesis](https://hypothesis.readthedocs.io/en/latest/) to write a
property-based test. Every test performs a sequence of randomly chosen steps
from the following list:

- allocate an object
- read a random field from a random object
- write a random reference into a random object
- drop a random stack reference
- perform one GC step
- allocate an array
- read a random index from a random array
- write to an array
- memcopy between two arrays

This approach of doing a sequence of steps is pretty close to the [stateful
testing](https://hypothesis.readthedocs.io/en/latest/stateful.html) approach of
hypothesis, but I just implemented it manually with the [data
strategy](https://hypothesis.readthedocs.io/en/latest/data.html#drawing-interactively-in-tests).

Every one of those steps is always performed on both the tested GC, and on some
regular Python objects. The Python objects provide the "ground truth" of what
the heap should look like, so we can compare the state of the GC objects
with the state of the Python objects to find out whether the GC made a mistake.

In order to check whether the test is actually useful, I reverted my bug fixes
and made sure that the test re-finds both the spurious GC assertion error and the
problems with memcopying an array.

In addition, the test also found corner cases in my fix. There was a situation
that I hadn't accounted for, which the test found after eventually.
I also plan on adding a bunch of other GC features as steps in the
test to stress them too (for example weakrefs, identity hashes, pinning, maybe
finalization).

At the point of publishing this post, the fixes got merged to the 2.7/3.9/3.10
branches of PyPy, and we'll have to do a release with the fixes at some point.


# The technical details of the bug

In order to understand the technical details of the bug, I need to give some
background explanations about PyPy's GC.

## PyPy's incremental GC

PyPy uses an incremental generational mark-sweep GC. It's
[generational](https://en.wikipedia.org/wiki/Tracing_garbage_collection#Generational_GC_(ephemeral_GC))
and therefore has minor collections (where only young objects get collected)
and major collections (collecting long-lived objects eventually, using a
[mark-and-sweep](https://en.wikipedia.org/wiki/Tracing_garbage_collection#Na%C3%AFve_mark-and-sweep)
algorithm). Young objects are allocated in a nursery using a
bump-pointer allocator, which makes allocation quite efficient. They are moved
out of the nursery by minor collections. In order to find references from old
to young objects the GC uses a write barrier to detect writes into old objects.

The GC is also
[incremental](https://en.wikipedia.org/wiki/Tracing_garbage_collection#Stop-the-world_vs._incremental_vs._concurrent),
which means that its major collections aren't done all at once (which would
lead to long pauses). Instead, major collections are sliced up into small
steps, which are done directly after a minor collection (the GC isn't
*concurrent* though, which would mean that the GC does work in a separate
thread).

The incremental GC uses [tri-color
marking](https://en.wikipedia.org/wiki/Tracing_garbage_collection#Tri-color_marking)
to reason about the reachable part of the heap during the marking phase, where
every old object can be:

- black: already marked, reachable, definitely survives the collection
- grey: will survive, but still needs to be marked
- white: potentially dead

The color of every object is encoded by setting flags
in the object header.

The GC maintains the **invariant** that black objects must never point to white
objects. At the start of a major collection cycle the stack roots are turned
gray. During the mark phase of a major collection cycle, the GC will trace gray
objects, until
none are left. To trace a gray object, all the objects it references have to be
marked grey if they are white so far. After a grey object is traced, it can be
marked black (because all the referenced objects are now either black or gray).
Eventually, there are no gray objects left. At that point (because no white
object can be reached from a black one) all the white objects are known to be
unreachable and can therefore be freed.

The GC is incremental because every collection step will only trace a limited
number of gray objects, before giving control back to the program. This leads to
a problem: if an already traced (black) object is changed between two marking
steps of the GC, the program can mutate that object and write a new reference
into one of its fields. This could lead to an invariant violation, if the
referenced object is white. Therefore, the GC uses the write barrier (which it
needs anyway to find references from old to young objects) to mark all black
objects that are modified gray, and then trace them again at one of the
later collection steps.

## The special write barrier of memcopy

Arrays use a different kind of write barrier than normal objects. Since they
can be arbitrarily large, tracing them can take a long time. Therefore it's
potentially wasteful to trace them fully at a minor collection. To fix this,
the array write barrier keeps more granular information about which parts of
the array have been modified since the last collection step. Then only the
modified parts of the array need to be traced, not the whole array.

In addition, there is another optimization for arrays, which is that memcopy is
treated specially by the GC. If memcopy is implemented by simply writing a loop
that copies the content of one array to the other, that will invoke the write
barrier every single loop iteration for the write of every array element,
costing a lot of overhead. Here's some pseudo-code:

```python
def arraycopy(source, dest, source_start, dest_start, length):
    for i in range(length):
        value = source[source_start + i]
        dest[dest_start + i] = value # <- write barrier inserted here
```

Therefore the GC has a special memcopy-specific
write barrier that will perform the GC logic once before the memcopy loop, and
then use a regular (typically SIMD-optimized) memcopy implementation from
`libc`. Roughly like this:

```python
def arraycopy(source, dest, source_start, dest_start, length):
    gc_writebarrier_before_array_copy(source, dest, source_start, dest_start, length)
    raw_memcopy(cast_to_voidp(source) + source_start,
                cast_to_voidp(dest) + dest_start,
                sizeof(itemtype(source)) * length)
```

(this is really a rough sketch. The [real
code](ttps://github.com/pypy/pypy/blob/789f964fff59c722b0872abcdc56d2b1373a9f3b/rpython/rlib/rgc.py#L365)
is much more complicated.)

## The bug

The bugs turned out to be precisely in this memcopy write barrier. When we
implemented the current GC, we adapted our previous GC, which was a
generational mark-sweep GC but *not* incremental. We started with most of the
previous GC's code, including the write barriers. The regular write barriers
were adapted to the new incremental assumptions, in particular the need for the
write barrier to also turn black objects back to gray when they are modified
during a marking phase. This was simply not done at all for the memcopy write
barrier, at least in two of the code paths. Fixing this problem fixes the unit
tests and stops the crashes.

# Reflections

The way the bug was introduced is really typical. A piece of code (the memcopy
write barrier) was written under a set of assumptions. Then those assumptions
changed later. Not all the code pieces that relied on these assumptions to be
correct were updated. It's pretty hard to prevent this in all situations.

I still think we could have done more to prevent the bug occurring. Writing a
property-based test for the GC would have been a good idea given the complexity
of the GC, and definitely something we did in other parts of our code at the
time (just using the `random` module mostly, we started using hypothesis
later).

It's a bit of a mystery to me why this bug managed to be undetected for so
long. Memcopy happens in a lot of pretty core operations of e.g. lists in
Python (`list.extend`, to name just one example). To speculate, I would suspect
that all the other preconditions for the bug occurring made it pretty rare:

- the content of an old list that is not yet marked needs to be copied into
  another old list that is marked already
- the source of the copy needs to also store an object that has no other
  references
- the source of the copy then needs to be overwritten with other data
- then the next collection steps need to be happening at the right points
- ...

Given the complexity of the GC logic I also wonder whether some lightweight
formal methods would have been a good idea. Formalizing some of the core
invariants in [B](https://en.wikipedia.org/wiki/B-Method) or
[TLA+](https://en.wikipedia.org/wiki/TLA%2B) and then [model
checking](https://en.wikipedia.org/wiki/Model_checking) them up to some number
of
objects would have found this problem pretty quickly. There are also correctness
proofs for GC algorithms in some research papers, but I don't have a good
overview of the literature to point to any that are particularly good or bad.
Going such a more formal route might have fixed this and probably a whole bunch
of other bugs, but of course it's a pretty expensive (and tedious) approach.

While it was super annoying to track this down, it was definitely good to learn
a bit more about how to use rr and the GDB scripting interface.

# Bonus Section: The Wrong Assertion

Some more technical information about the wrong assertion is in this section.

## Background: pre-built objects

PyPy's VM-building bootstrapping process can "freeze" a bunch of heap objects
into the final binary. This allows the VM to start up quickly, because those
frozen objects are loaded by the OS as part of the binary.

Those frozen pre-built objects are parts of the 'roots' of the garbage
collector and need to be traced. However, tracing all the pre-built objects at
every collection would be very expensive, because there are a lot of them
(about 150,000 in a PyPy 3.10 binary). Tracing them all is also not necessary,
because most of them are never modified. Therefore they only have references to
other pre-built objects, which can never be deallocated anyway. Therefore we
have an optimization that uses the write barrier (which we need anyway to find
old-to-young pointers) to notice when a pre-built object gets modified for the
very first time. If that happens, it gets added to the set of pre-built objects
that gets counted as a root, and is therefore traced as a root at collections
from then on.

## The wrong assertion

The assertion that triggered when I turned on the GC debug mode was saying that
the GC found a reference from a black to a white object, violating its
invariant. Unmodified pre-built objects count as black, and they aren't roots,
because they can only ever reference other pre-built objects. However, when a
pre-built object gets modified for the first time, it becomes part of the root
set and will be marked gray. This logic works fine.

The wrong assertion triggers if a pre-built object is mutated for the very
first time in the middle of an incremental marking phase. While the pre-built
object gets added to the root set just fine, and will get traced before the
marking phase ends, this is encoded slightly differently for pre-built objects,
compared to "regular" old objects. Therefore, the invariant checking code
wrongly reported a black->white pointer in this situation.

To fix it I also wrote a unit test checking the problem, made sure that the GC
hypothesis test also found the bug, and then fixed the wrong assertion to take
the color encoding of pre-built objects into account.

The bug managed to be invisible because we don't tend to turn on the GC
assertions very often. We only do that when we find a GC bug, which is of
course also when we need it the most to be correct.

# Acknowledgements

Thanks to Matti Picus, Max Bernstein for giving me feedback on drafts of the
post. Thanks to Armin Rigo for reviewing the code and pointing out holes in my
thinking. Thanks to the original reporters of the various forms of the bug,
including Lily Foote, David Hewitt, Wenzel Jakob.
