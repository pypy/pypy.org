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

A few weeks ago, [Shriram Krishnamurthi](https://cs.brown.edu/~sk/) [asked on
Twitter](https://twitter.com/ShriramKMurthi/status/1818009884484583459):

"I'm curious what the current state of tracing JITs is. They used to be all the
rage for a while, then I though I heard they weren't so effective, then I
haven't heard of them at all. Is the latter because they are ubiquitous, or
because they proved to not work so well?"

I replied with my personal (partly pretty subjective) opinions about the
question in a lengthy Twitter thread (which also spawned an even lengthier
discussion). I wanted to turn what I wrote there into a blog post to make it
more widely available. The blog post i still somewhat terse, I've tried to at
least add links to further information. Please ask in the comments if something
is particularly unclear.


## Meta-tracing

First some personal context: my perspective is informed by nearly two decades
of work on PyPy. PyPy's implementation language, RPython, has support a
meta-JIT, which allows it to re-use its JIT infrastructure for the various
Python versions that we support (currently we do releases of PyPy2.7 and
PyPy3.10 together). We have also used the meta-JIT infrastructure for some
experimental different languages like Prolog, Racket, a database (those
implementations had various degrees of maturity and most of them are research
software and aren't maintained any more), but also some more surprising things
like an ARM and RISC-V emulator.

PyPy gives itself the goal to try to be extremely compatible with all the
quirks of the Python language. We don't change the Python language to make
things easier to compile. We try very hard to have no opinions on language
design. The CPython core developers come up with the semantics, we somehow deal
with them.

PyPy started using a tracing JIT approach *not* because we thought method-based
just-in-time compilers are bad. Historically we had tried to implemend a
method-based meta-JIT that was partial evaluation (we wrote three or four
method-based prototypes that all weren't as good as we hoped). After all those
experiments failed we switched to the tracing approach, and only at this point
did our meta-JIT start producing interesting performance.

In the meta-JIT context tracing has good propreties, because tracing has
relatively understandable behavior and its easy(ish) to tweak how things work
with extra annotations in the interpreter source.

Another reason why meta-tracing often works well for PyPy is that it can often
slice through the complicated layers of Python quite effectively and remove a
lot of overhead. Python is often described as simple, but I think that's
actually a misconception. On the implementation level it's a very big and
complicated language, and it is also continuously getting new features every
year (the language is quite a bit more complicated than Javascript, for
example).


### Truffle

Later Truffle came along and made a method-based meta-JIT using partial
evaluation work. However Truffle (and Graal) has had significantly more people
working on it and much more money invested. In addition, it at first required a
quite specific style of AST-based interpreters (in the last few years they have
also started supporting bytecode-based interpreters).

It's still my impression that getting similar results with Truffle is a lot
more work for language implementers than with RPython, and the warmup of
Truffle can often pretty bad. But Truffle is definitely an existence proof that
meta-JITs don't *have* to be based on tracing.


## Tracing, the good

Let's now discuss some of the advantages of tracing that go beyond the ease of
using tracing for a meta-JIT.

Tracing allows for doing very aggressive partial inlining, following just the
hot path through lots of layers of abstraction, is obviously often really
useful for generating fast code

It's definitely possible to achieve the same effect in a method-based context
with path splitting. But it requires a lot more implementation work and is not
trivial, because the path execution counts of inlined functions can often be
very call-site dependent, and tracing gives you call-site dependent path
splitting "for free".

(The aggressive partial inlining and path splitting is even more important in
the meta-tracing context of PyPy, where some of inlined layers are a part of
the language runtime, and where rare corner cases that are never executed in
practice are basically absolutely everywhere.)

Another advantage of tracing is that it makes a whole bunch of optimizations
really easy to implement, because there are (to first approximation) no control
flow merges. This makes all the optimizations that we do (super-)local
optimizations, that operate on a single (very long) basic block. This the JIT
to do the optimizations in exactly one forwards and one backwards pass. Eg our
allocation removal/partial escape analysis is simple.

This ease of implementation of optimizations allowed us to implement some
pretty decent optimizations. Our optimization of temporary allocations, the way
we can reason about the heap, about dictionary accesses, about properties of
functions of the runtime, about the range and known bits of integer variables
is all quite solid.


## Tracing, the bad

Tracing also comes with a significant number of downsides. Probably the biggest
one is that it tends to have big performance cliffs (PyPy certainly has them,
and other tracing JITs such as TraceMonkey had them too). The 'good' cases are
really good, but if something goes wrong you are annoyed and performance can
become a lot slower. With a simple method jit the performance is often much
more "even".

Another set of downsides is that tracing has a number of corner cases and
"weird" behaviour in certain situations. Questions such as:
- When do you stop inlining?
- What happens when you trace recursion?
- What happens if your traces are consistently too long, even without inling?
- and so on...

There are also some classes of programs that tend to perform quite poorly when
they are executed by a tracing JIT, bytecode interpreters in particularly, and
other extremely unpredictably branchy code. This is because the core assumption
of the tracing jit "loops take similar control flow paths" is just really wrong
in the case of interpreters.


## Discussion

The Twitter thread spawned quite a bit of discussion, please look at the
original thread. Here are three that I wanted to highlight:

"This is a really great summary. Meta-tracing is probably the one biggest
success story. I think it has to do with how big and branchy the bytecode
implementations are for typical dynamic languages; the trace captures latent
type feedback naturally.

There is an upper limit, tho." [Ben Titzer](https://twitter.com/TitzerBL/status/1818385622203298265)

I agree with this completely, the complexity of Python bytecodes is a big
factor for why meta tracing works well for us. But also in Python there are
many builtin types (collection types, types that form the meta-object protocol
of Python, standard library modules implemented in C/RPython) and tracing
operations on them is very important too, for good performance.


----

"I think Mozilla had a blog post talking more about the difficulty with
TraceMonkey, could only find this one:
https://blog.mozilla.org/nnethercote/category/jagermonkey/"

[Stefan Marr](https://twitter.com/smarr/status/1818600052752797990)

"imo doing tracing for JS is really hard mode, because the browser is so
incredibly warmup-sensitive. IIRC tracemonkey used a really low loop trip count
(single-digit?) to decide when to start tracing (pypy uses >1000). the JS
interpreters of the time were also quite slow."

[me](https://twitter.com/cfbolz/status/1818609594219811245)

----

"There are a number of corner cases you have to deal with in a tracing JIT. It's
unfortunately not as simple and easy as the initial papers would have you
believe. One example is how would you deal with a loop inside a loop? Is your
tracing now recursive?

There's been some research work on trace stitching to deal with trace explosion
but it does add complexity. With the increase in complexity, I think most
industrial VM developers would rather pick tried-and-true method-based JITs
that are well understood."

[Maxime Chevalier](https://twitter.com/Love2Code/status/1818292516753383644)

## Conclusion

In a non-meta-jit it's very unclear to me that you should use tracing. It makes
more sense to rather spend effort on a solid control-flow-graph-based baseline
and then try to get some of the good properties of tracing on top (path
splitting, partial inlining, etc).

For PyPy with it's meta-JIT I still think tracing is a relatively pragmatic
choice, and in the cases where it works well the performance of PyPy is quite
hard to beat (particularly with the constraint of not being "allowed" to change
the language).

All of the above is all purely based on the data point of a single project, of
course, but one that has implemented a number of different languages.

(A side point: people who haven't worked on Python tend to underestimate
its complexity. A pet peeve of mine is C++ compiler devs/static
analysis/Javascript people/other well-meaning communities coming with
statements like "why don't you just..."  🤷‍♀️)
