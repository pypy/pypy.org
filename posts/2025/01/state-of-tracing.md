<!--
.. title: Musings on Tracing in PyPy
.. slug: musings-tracing
.. date: 2025-01-05 17:01:09 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: CF Bolz-Tereick
-->

Last summer, [Shriram Krishnamurthi](https://cs.brown.edu/~sk/) [asked on
Twitter](https://twitter.com/ShriramKMurthi/status/1818009884484583459):

> "I'm curious what the current state of tracing JITs is. They used to be all the
> rage for a while, then I though I heard they weren't so effective, then I
> haven't heard of them at all. Is the latter because they are ubiquitous, or
> because they proved to not work so well?"

I replied with my personal (pretty subjective) opinions about the
question in a lengthy Twitter thread (which also spawned an even lengthier
discussion). I wanted to turn what I wrote there into a blog post to make it
more widely available (Twitter is no longer easily consumable without an
account), and also because I'm mostly not using Twitter anymore. The blog post
i still somewhat terse, I've written a small background section and tried to at
least add links to further information. Please ask in the comments if something
is particularly unclear.


## Background

I'll explain a few of the central terms of the rest of the post. *JIT compilers*
are compilers that do their work at runtime, interleaved (or concurrent with)
the execution of the program. There are (at least) two common general styles of
JIT compiler architectures. The most common one is that of a method-based JIT,
which will compile one method or function at a time. Then there are tracing JIT
compilers, which generate code by tracing the execution of the user's program.
They often focus on loops as stheir main unit of compilation.

Then there is the distinction between a "regular" JIT compiler and that of a
*meta-JIT*. A regular JIT is built to compile one specific source language to
machine code. A meta-JIT is a framework for building JIT compilers for a
variety of different languages, re-using as much machinery as possible between
the different implementation.

## Personal and Project Context

Some personal context: my perspective is informed by nearly [two
decades](https://mail.python.org/archives/list/pypy-dev@python.org/thread/TZM37YJ733G445R6JGTV26333RQEPLRX/)
of work on PyPy. PyPy's implementation language, [RPython](https://rpython.readthedocs.io/), has support for a
meta-JIT, which allows it to re-use its JIT infrastructure for the various
Python versions that we support (currently we do releases of PyPy2.7 and
PyPy3.10 together). Our meta-JIT infrastructure has been used for some
experimental different languages like:

- PyPy's [regular expression engine](https://pypy.org/posts/2010/11/pypy-14-ouroboros-in-practice-5437628000869417542.html#more-highlights)
- [RPySom](https://github.com/SOM-st/PySOM), a tiny Smalltalk
- [Ruby](https://github.com/topazproject/topaz)
- [PHP](https://github.com/hippyvm/hippyvm)
- [Prolog](https://dl.acm.org/doi/10.1145/1836089.1836102),
- [Racket](https://dl.acm.org/doi/10.1145/2784731.2784740),
- a [database (SQLite)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol056-ecoop2016/LIPIcs.ECOOP.2016.4/LIPIcs.ECOOP.2016.4.pdf)
- [Lox](https://www.youtube.com/watch?v=fZj3uljJl_k), the language of [Crafting Interpreters](https://craftinginterpreters.com/)
- an [ARM and RISC-V emulator](https://docs.pydrofoil.org/en/latest/)
- and many more

Those implementations had various degrees of maturity and many of them are
research software and aren't maintained any more.

PyPy gives itself the goal to try to be extremely compatible with all the
quirks of the Python language. We don't change the Python language to make
things easier to compile and we support the introspection and debugging
features of Python. We try very hard to have no opinions on language design.
The CPython core developers come up with the semantics, we somehow deal with
them.

## Meta-tracing

PyPy started using a [tracing
JIT](https://en.wikipedia.org/wiki/Tracing_just-in-time_compilation) approach
*not* because we thought method-based just-in-time compilers are bad.
Historically we [had
tried](https://foss.heptapod.net/pypy/extradoc/-/blob/branch/extradoc/eu-report/D08.2_JIT_Compiler_Architecture-2007-05-01.pdf)
to implemend a method-based meta-JIT that was using partial evaluation (we wrote
three or four method-based prototypes that all weren't as good as we hoped).
After all those [experiments
failed](https://pypy.org/posts/2008/10/sprint-discussions-jit-generator-3301578822967655604.html)
we switched to the [tracing
approach](https://dl.acm.org/doi/10.1145/1565824.1565827), and only at this
point did our meta-JIT start producing interesting performance.

In the meta-JIT context tracing has good properties, because tracing has
relatively understandable behavior and its easy(ish) to tweak how things work
[with extra annotations in the interpreter
source](https://dl.acm.org/doi/10.1145/2069172.2069181).

Another reason why meta-tracing often works well for PyPy is that it can often
slice through the complicated layers of Python quite effectively and remove a
lot of overhead. Python is often described as simple, but I think that's
actually a misconception. On the implementation level it's a very big and
complicated language, and it is also continuously getting new features every
year (the language is quite a bit more complicated than Javascript, for
example[^help]).

[^help]: (A side point: people who haven't worked on Python tend to
    underestimate its complexity and pace of development. A pet peeve of mine
    is C++ compiler devs/static analysis/Javascript people/other well-meaning
    communities coming with statements like "why don't you just..."  🤷‍♀️)


### Truffle

Later [Truffle](https://dl.acm.org/doi/abs/10.1145/2509578.2509581) came along
and made a method-based meta-JIT using partial evaluation work. However Truffle
(and [Graal](https://www.oracle.com/java/graalvm/)) has had significantly more people working on it and much more
money invested. In addition, it at first required a quite specific style of
[AST-based interpreters](https://dl.acm.org/doi/10.1145/2384577.2384587) (in
the last few years they have also added support for bytecode-based
interpreters).

It's still my impression that getting similar results with Truffle is [more
work for language
implementers](https://stefan-marr.de/downloads/oopsla15-marr-ducasse-meta-tracing-vs-partial-evaluation.pdf)
than with RPython, and the [warmup](https://arxiv.org/pdf/1602.00602) of
Truffle can often pretty bad. But Truffle is definitely an existence proof that
meta-JITs don't *have* to be based on tracing.


## Tracing, the good

Let's now actually get to he heart of Shriram's question and discuss some of
the advantages of tracing that go beyond the ease of using tracing for a
meta-JIT.

Tracing allows for doing very aggressive [partial
inlining](https://www.cs.fsu.edu/~xyuan/INTERACT-15/papers/paper11.pdf),
Following just the hot path through lots of layers of abstraction is obviously
often really useful for generating fast code.

It's definitely possible to achieve the same effect in a method-based context
with [path splitting](https://dl.acm.org/doi/pdf/10.1145/117954.117955). But it
requires a lot more implementation work and is not trivial, because the path
[execution counts](https://dl.acm.org/doi/10.1145/504282.504295) of inlined
functions can often be very call-site dependent. Tracing, on the other hand,
gives you call-site dependent path splitting "for free".

(The aggressive partial inlining and path splitting is even more important in
the meta-tracing context of PyPy, where some of inlined layers are a part of
the language runtime, and where rare corner cases that are never executed in
practice are everywhere.)

Another advantage of tracing is that it makes a number of optimizations
really easy to implement, because there are (to first approximation) no control
flow merges. This makes all the optimizations that we do (super-)[local
optimizations](https://en.wikipedia.org/wiki/Optimizing_compiler#Local_vs._global_scope),
that operate on a single (very long) basic block. This allows the JIT to do the
optimizations in exactly one forwards and one backwards pass. An example is our
[allocation removal](https://dl.acm.org/doi/10.1145/1929501.1929508)/partial
escape analysis pass, which is [quite
simple](https://pypy.org/posts/2022/10/toy-optimizer-allocation-removal.html),
whereas the [version for general control
flow](https://ssw.jku.at/Teaching/PhDTheses/Stadler/Thesis_Stadler_14.pdf) has
a lot more complexity, particularly in its handling of loops.

This ease of implementation of optimizations allowed us to implement some
pretty decent optimizations. Our allocation removal, the way PyPy's JIT can
reason about the heap, about dictionary accesses, about properties of functions
of the runtime, about the range and [known bits of integer
variables](https://pypy.org/posts/2024/08/toy-knownbits.html) is all quite
solid.


## Tracing, the bad

Tracing also comes with a significant number of downsides. Probably the biggest
one is that it tends to have big performance cliffs (PyPy certainly has them,
and other tracing JITs such as TraceMonkey had them too). In my experience the
'good' cases of tracing are really good, but if something goes wrong you are
annoyed and performance can become a lot slower. With a simple method JIT the
performance is often much more "even".

Another set of downsides is that tracing has a number of corner cases and
"weird" behaviour in certain situations. Questions such as:
- When do you stop inlining?
- What happens when you [trace recursion](https://mail.python.org/archives/list/pypy-dev@python.org/thread/GQQ7ABUFHGEAHWN7RQZM6D54CDROQINR/)?
- What happens if your traces are [consistently too long, even without inling](https://pypy.org/posts/2021/09/jit-auto-generated-code.html)?
- and so on...

Some of these problems can be solved by adding heuristics to the tracing JIT,
but doing so loses a lot of the simplicity of tracing again.

There are also some classes of programs that tend to generally perform quite
poorly when they are executed by a tracing JIT, bytecode interpreters in
particularly, and other extremely unpredictably branchy code. This is because
the core assumption of the tracing jit "loops take similar control flow paths"
is just really wrong in the case of interpreters.


## Discussion

The Twitter thread spawned quite a bit of discussion, please look at the
original thread for all of the comments. Here are three that I wanted to
highlight:

> "This is a really great summary. Meta-tracing is probably the one biggest
> success story. I think it has to do with how big and branchy the bytecode
> implementations are for typical dynamic languages; the trace captures latent
> type feedback naturally.
>
> There is an upper limit, tho."

[Ben Titzer](https://twitter.com/TitzerBL/status/1818385622203298265)

I agree with this completely. The complexity of Python bytecodes is a big
factor for why meta tracing works well for us. But also in Python there are
many builtin types (collection types, types that form the [meta-object
protocol](https://en.wikipedia.org/wiki/Metaobject#Metaobject_protocol) of
Python, standard library modules implemented in C/RPython) and tracing
operations on them is very important too, for good performance.


----

> "I think Mozilla had a blog post talking more about the difficulty with
> TraceMonkey, could only find this one:
> https://blog.mozilla.org/nnethercote/category/jagermonkey/"

[Stefan Marr](https://twitter.com/smarr/status/1818600052752797990)

> "imo doing tracing for JS is really hard mode, because the browser is so
> incredibly warmup-sensitive. IIRC tracemonkey used a really low loop trip count
> (single-digit?) to decide when to start tracing (pypy uses >1000). the JS
> interpreters of the time were also quite slow."

[me](https://twitter.com/cfbolz/status/1818609594219811245)

In the meantime there were some more reminiscences about tracing in Javascript
by [Shu-Yu Guo in a panel
discussion](https://www.youtube.com/live/_VF3pISRYRc?t=24797s) and by [Jason
Orendorff on Mastodon](https://kfogel.org/notice/AngH0uqyJl231yLLOa).

----

> "There are a number of corner cases you have to deal with in a tracing JIT. It's
> unfortunately not as simple and easy as the initial papers would have you
> believe. One example is how would you deal with a loop inside a loop? Is your
> tracing now recursive?

> There's been some research work on trace stitching to deal with trace explosion
> but it does add complexity. With the increase in complexity, I think most
> industrial VM developers would rather pick tried-and-true method-based JITs
> that are well understood."

[Maxime Chevalier](https://twitter.com/Love2Code/status/1818292516753383644)


## Conclusion

Given access to enough developers and in the context of "normal" jitting (ie
not meta-jitting) it's very unclear to me that you should use tracing. It makes
more sense to rather spend effort on a solid control-flow-graph-based baseline
and then try to get some of the good properties of tracing on top (path
splitting, partial inlining, partial escape analysis, etc).

For PyPy with its meta-JIT (and the fact that we don't have particularly much
funding nor people) I still think tracing was/is a relatively pragmatic choice.
When I talked with [Sam Tobin-Hochstadt](https://samth.github.io/) about this
topic recently he characterized it like this: "tracing is a labor-saving device
for compiler authors".

Performance-wise PyPy is still quite hard to beat in the cases where it works
well (i.e. pure Python code that doesn't use too many C modules, which are
[supported but slow in
PyPy](https://pypy.org/posts/2018/09/inside-cpyext-why-emulating-cpython-c-8083064623681286567.html)).
In general, there are very few JITs for Python (particularly with the
constraint of not being "allowed" to change the language), the most competitive
other ones are [GraalPy](https://www.graalvm.org/python/), also based on a
meta-JIT approach. Instagram is running on
[Cinder](https://github.com/facebookincubator/cinder/) and also CPython has
[grown a JIT
recently](https://tonybaloney.github.io/posts/python-gets-a-jit.html) which
was part of the recent [3.13 release, but only as an off-by-default build
option](https://docs.python.org/3.13/whatsnew/3.13.html#an-experimental-just-in-time-jit-compiler),
so I'm very excited about how Python's performance will develop in the next
years!

