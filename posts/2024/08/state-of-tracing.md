<!--
.. title: The State of Tracing
.. slug: mining-jit-traces-missing-optimizations-z3
.. date: 2024-08-01 17:01:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: CF Bolz-Tereick
-->



"I'm curious what the current state of tracing JITs is. They used to be all the
rage for a while, then I though I heard they weren't so effective, then I
haven't heard of them at all. Is the latter because they are ubiquitous, or
because they proved to not work so well?"

https://twitter.com/ShriramKMurthi/status/1818009884484583459

my opinion on tracing. this is such a complicated question, kind of too large for twitter. here's a thread that should be a blog post, with sections:


## Meta-tracing

personal context: been working on pypy since ~20 years. pypy has a meta-JIT,
which allows it to re-use jit infrastructure for the various Python versions,
and also for some experimental different languages like Prolog, Racket, also an
ARM and RISC-V emulator

PyPy gives itself the goal to try to be extremely compatible with all the
quirks of the Python language. so changing the language to make things easier
to compile is a no no. we try hard to have no opinions on language design, they
come up with the semantics, we somehow deal.

PyPy started using a tracing JIT approach *not* because we thought method jits
are bad. but because we had failed to do a method-based meta-JIT that was using
partial evaluation (we wrote three or four method-based prototypes that all
weren't as good as we hoped).

In the meta-JIT context tracing is nice, because tracing has relatively
understandable behavior and its easy(ish) to tweak how things work with extra
annotations in the interpreter source.

meta-tracing often works well for us/pypy. It can often slice through the
complicated layers of Python quite effectively and remove a lot of overhead
(Python is more complicated than JS, imo. it's big and complex and growing)

### Truffle

later truffle came along and made a method-based meta-JIT using partial
evaluation work, but with a lot more people/resources and at first requiring a
quite specific style of interpreters

it's still my impression that getting similar results with truffle is a lot
more work than with rpython and the warmup of truffle can often pretty bad. but
both are questions more for @smarr again

## Tracing, the good

the aggressive partial inlining of tracing, following just the hot path through
lots of layers of abstraction, is obviously often really useful for generating
fast code

it should be possible to achieve the same effect in a method-based context with
path splitting. but it's not trivial, because the path execution counts of
inlined functions can often be very call-site dependent, and tracing gives you
call-site dependent path splitting

(the aggressive partial inlining and path splitting is even more important in
the meta-tracing context of pypy, where some of layers are part of the runtime,
and where  rare corner cases are basically absolutely everywhere)

tracing makes a whole bunch of optimizations really easy to implement, because
there are (to first approximation) no control flow merges. This allows us to do
optimizations in exactly one forwards and one backwards pass. Eg our allocation
removal/partial escape analysis is simple

in a tracing jit it can therefore be quite easy to get some pretty decent
optimizations. Our optimization of temporary allocations, the way we can reason
about the heap, about dictionary accesses, about properties of functions of the
runtime is all quite decent


## Tracing, the bad

downsides of tracing: in my experience it tends to have big performance cliffs.
The 'good' cases are really good, but if something goes wrong you are annoyed
and performance can become a lot slower. with a simple method jit perf is more
"even"

there are a bunch of strange corner cases that tracing has (when do you stop
inlining, what about tracing recursion, what happens if your traces are too
long, stuff like that)

I agree with this too (and @samth and I have discussed it a few times when
working on Pycket): if you trace the bytecode dispatch loop of a bytecode
interpreter (or other interpreter-like control flow), you will get not great
results

https://twitter.com/pnguyen0112/status/1818100321652199456

this is because the core assumption of the tracing jit "loops take similar
control flow paths" is just really wrong in the case of interpreters


this is because the core assumption of the tracing jit "loops take similar
control flow paths" is just really wrong in the case of interpreters



## Discussion

"This is a really great summary. Meta-tracing is probably the one biggest
success story. I think it has to do with how big and branchy the bytecode
implementations are for typical dynamic languages; the trace captures latent
type feedback naturally.

There is an upper limit, tho."

https://twitter.com/TitzerBL/status/1818385622203298265

Exactly, the complexity of py bytecodes is a big factor for why meta tracing
works well for us. But also in python there are many builtin types (collection
types, types that form the mop, stdlib modules implemented in C/rpython) and
tracing operations on them is important too

Stefan Marr:
"I think Mozilla had a blog post talking more about the difficulty with
TraceMonkey, could only find this one:
https://blog.mozilla.org/nnethercote/category/jagermonkey/"
https://twitter.com/smarr/status/1818600052752797990

imo doing tracing for JS is really hard mode, because the browser is so
incredibly warmup-sensitive. IIRC tracemonkey used a really low loop trip count
(single-digit?) to decide when to start tracing (pypy uses >1000). the JS
interpreters of the time were also quite slow.

Max Bernstein:
"What about basic block versioning?"
https://twitter.com/tekknolagi/status/1818368411157905482

It's another point in the phase space ;-). I like it a lot, and maybe it could
be pushed really far to give the best of both cfg-based and tracing approaches.
I'd be curious to see a BBV-based meta-JIT (but unfortunately writing meta-JITs
is super expensive in terms of time).

Maxime Chevalier:
"There are a number of corner cases you have to deal with in a tracing JIT. It's
unfortunately not as simple and easy as the initial papers would have you
believe. One example is how would you deal with a loop inside a loop? Is your
tracing now recursive?

There's been some research work on trace stitching to deal with trace explosion
but it does add complexity. With the increase in complexity, I think most
industrial VM developers would rather pick tried-and-true method-based JITs
that are well understood."

https://twitter.com/Love2Code/status/1818292516753383644

## Conclusion

In a non-meta-jit it's very unclear to me that you should use tracing. Rather
spend effort on a solid cfg-based baseline and then try to get some of the good
properties of tracing on top (path splitting, partial inlining, etc)

in the meta-jit of pypy context I still think it's a relatively pragmatic
choice, and in the cases where it works well the performance of pypy is quite
hard to beat (particularly with the constraint of not being "allowed" to change
the language)

this is all purely based on the data point of a single project, of course,
albeit one that has implemented a whole bunch of different languages. please
everyone tell me if you disagree with me.

a side point: nobody in the current thread did this, but people who haven't
worked on python tend to underestimate its complexity. A pet peeve of mine is
C++ compiler devs/static analysis people/other well-meaning communities coming
with statements like "why don't you just..."  🤷‍♀️


