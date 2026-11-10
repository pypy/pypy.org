.. title: 20 Years of Pyrolog
.. slug: 20-years-of-pyrolog
.. date: 2026-11-08 14:16:45 UTC+01:00
.. tags: 
.. category: 
.. link: 
.. description: 
.. type: text
.. author: CF Bolz-Tereick


On November 12, 2006 I did the `first surviving commit`_ of my RPython based
Prolog implementation **Pyrolog** into the PyPy repository. I had been working
on it since spring 2006 already. In that year we were finishing up the first
PyPy EU research project and I was finishing up my Bachelor studies at Uni
Düsseldorf. Since it's now 20 years later I wanted to write a personal
retrospective post on this project. Pyrolog never had any real users, but it
still led to some interesting research and influenced a number of other RPython
projects.

.. contents:: Contents
   :depth: 2
   :backlinks: none

Context
========

As part of the EU project we had promised lots of things, including
implementing some constraint programming in PyPy. For this strand of the work I
learned Prolog by reading Clocksin and Mellish's Programming Prolog [CM2003]_
and later the Art of Prolog [SS1994]_.

In March 2006, the PyPy project partner `Logilab`_ organized a sprint in UCLouvain
in Louvain-la-Neuve (Belgium), with `Peter van Roy`_ and some of the researchers
working on `Gecode`_. The plan was to add some kind of unification and constraint
solving to PyPy. The Logilab people were quite inspired by the Van Roy/Haridi
book [VH2004]_ and I later studied his Prolog implementation survey paper
[VanRoy1994]_.

In 2006 I also attended my advisor `Michael Leuschel's`_ Prolog lectures in
Düsseldorf. During that I started working on a Prolog interpreter in RPython,
later called Pyrolog. Much of the early commit history is lost unfortunately,
it didn't make the `Subversion->Mercurial`_ jump correctly and I don't know
where the codespeak archives are now.

.. _`Subversion->Mercurial`: https://pypy.org/posts/2010/12/pypy-migrates-to-mercurial-3308736161543832134.html

2006/2007 The first year 
==========================

Pyrolog's first incarnation had a fairly straightforward implementation of
unification in object-oriented RPython code. Logical variables stored an index,
with their bindings stored in a global array at that index.

.. figure:: /images/2026-pyrolog-memory-orig.svg
   :alt: Memory layout of the interpreter
   :width: 90%

   Pyrolog Memory Layout from [Bolz2007]_

That version represented choice points by having exception handlers on the
interpreter level, and backtracking via throwing exceptions, catching them
further up. It used a continuation-based architecture for storing the calls
left to do. Those success continuations were stored on the heap and
continuously allocated and consumed. This approach was taken from Paul Tarau's
BinProlog ([TB1990]_, [Tarau1992]_) and also based on some other Prolog papers
[Lindgren1994]_ [Neumerkel1995]_.

To deal with deep recursion that Prolog programs typically do, that version of
Pyrolog relied on RPython's *stackless transformation* [BR2007D071]_, which
would unwind the host stack (i.e. the C stack) and store its information on the
host heap if host stack overflow was getting close. When storing C stack frames
on the heap in this way, we also did some amount of tail call optimization. We
were super into this idea at the time. However, it turned out not to be too
practical, making the binary twice as large and slower, so eventually we
removed it again.

I also experimented with using the first RPython JIT on that version of
Pyrolog. That JIT was a partial-evaluation-based method JIT and managed to
speed up some small Python programs. I don't think it did very much for Pyrolog
though.

The performance of that version of Pyrolog was quite disappointing. In my B.Sc.
thesis [Bolz2007]_ I did some measurements against `SWI`_ and `Sicstus Prolog`_.
Sicstus was often an order of magnitude faster than Pyrolog at this point.

In the thesis I also implemented a way to call into Prolog from Python code and
had a case study where I implemented a Tic-Tac-Toe GUI in Python, with the game
logic in Prolog.

Shortly after finishing my thesis, I `changed the variable representation`_:
instead of indexing into a global binding array, each variable object stored
its own binding. The exception-based backtracking architecture stayed in place
for another two years.

2008/2009 JIT developments on the PyPy side
============================================

After the EU project finished we started working on various new architectural
ideas for the RPython meta-JIT. Armin Rigo, me and some others wrote two new
prototypes. We weren't happy with them, so in 2008 Armin and I started
experimenting with a prototype for a new trace-based JIT `written in Prolog`_. We
used Prolog because its pattern matching and ease of meta-programming allowed
us to experiment more easily with different designs.

Towards the end of 2008 and
throughout 2009 Armin, Maciej Fijałkowski, me and others started porting the
design back to RPython and called it pyjitpl5_ (the "pl" in the name stands for
"Prolog"). This is still the base of the current PyPy meta-JIT compiler and
became the subject of the second (smaller) PyPy EU project in the Eurostars_
program.

We eventually published a paper about the Prolog version of the JIT [BLR2010]_
at LOPSTR 2009.

.. _`written in Prolog`: https://pypy.org/posts/2008/06/hi-all-some-news-from-jit-front-7534695765973581706.html
.. _Eurostars: https://pypy.org/posts/2010/12/oh-and-btw-pypy-gets-funding-through.html

2009-2010 New Pyrolog Architecture: More Continuations
========================================================

After working mostly on PyPy and the new JIT in 2008 and 2009 I started working
on Pyrolog again over the 2009 Christmas break. Since the stackless
transformation wasn't compatible with the new JIT I had to switch to a
different architecture, still used today. The first version of the Pyrolog
architecture had already stored success continuations on the heap. The goal of this
refactoring was to also store the *failure continuations* as `reified RPython
objects`_.

.. code:: python

    # the simplified main interpreter loop

    def interpret(sc, fc, trail):
        while not sc.is_done():
            try:
                sc, fc, trail = sc.activate(fc, trail)
            except UnificationFailed:
                sc, fc, trail = fc.fail(trail)

This had the effect that the host stack use is completely flat when
interpreting Prolog calls. The state needed to continue with Prolog execution is always
stored in continuation objects on the heap. The interpreter is therefore
dealing with two continuations, one activated upon success, and one on failure.

Additionally, there is a (segmented) trail object which stores the variable
bindings that need to be undone when backtracking. Failure continuations have a
reference to the part of the trail they need to backtrack to, when activated.

The downside of this approach is that the interpreter continuously has to
allocate heap data for all the success and failure continuations. This puts a
lot of pressure on the RPython GC. Also, term unification still uses the host
stack, so unifying very deep terms can still be a problem and lead to
implementation-level recursion errors.


JIT support
----------------

The real goal of the refactoring was to make the interpreter more JIT-friendly.
Since the interpreter doesn't use recursion for Prolog calls any more, the loops at the Prolog
level (expressed as recursion) can be traced by the JIT. All the continuous
allocations of continuations can be optimized by the allocation removal of the
RPython JIT. If all this works correctly, the performance of Pyrolog becomes
very good, often beating Sicstus by a significant factor on suitable
microbenchmarks.

.. figure:: /images/2026-pyrolog-vmgen.svg
   :width: 50%

   Pyrolog VM Generation vs. Runtime from [BLS2010]_

Unfortunately this is mainly the case for code with very predictable control
flow, ideally with nice loops. Since the main appeal of Prolog is to do
backtracking search, control flow is typically not very predictable for
interesting more Prolog-like programs. As soon as the control flow becomes too
complicated and unpredictable, the continuations survive beyond the region that
the JIT optimizes and have to be allocated on the heap again. Therefore Pyrolog has
quite extreme performance cliffs.

We wrote a paper about this version of Pyrolog for PPDP 2010 [BLS2010]_ (together with
Michael Leuschel and my later colleague David Schneider). That conference
was super interesting and important for me. I met Paul Tarau (who invented
BinProlog, one of the inspirations of Pyrolog. He later gave an excellent `Prolog
talk`_ at the virtual machine summer school in 2016), Olivier Danvy (whose
paper [BD2004]_ I should have cited. Genuinely one of the nicest people),
Kenichi Asai (who had worked on partial evaluation and reflection) and several
others. At that point during my PhD I was feeling relatively demotivated, and
my chats with these researchers were incredibly encouraging.

.. _`Prolog talk`: https://www.youtube.com/watch?v=SRYAMt8iQSw

.. figure:: https://www3.risc.jku.at/conferences/ppdp2010/photos/img_8487.jpg

   `Group photo at PPDP 2010`_

.. _`Group photo at PPDP 2010`: https://www3.risc.jku.at/conferences/ppdp2010/photos/index.html

On the bus trip to Gmunden, where the conference dinner took place, somebody
explained how to implement unification of cyclic terms (i.e. rational trees) to
me. Unfortunately I am not quite sure who it was any more, I think it might
have been Thierry Martinez. This led to me `implementing support for cyclic
term unification`_. I still like that trick a lot and tried to explain it to
`Phil Zucker`_ earlier this year. I hope to blog about it eventually. For a fun
use case see my blog post on `rational tree unification for dfa minimization`_.

.. _`Phil Zucker`: https://www.philipzucker.com/
.. _`rational tree unification for dfa minimization`: https://cfbolz.de/posts/dfa-minimization-using-rational-trees-in-prolog/

2011/2012 Widening Prolog support
==================================

During 2011 and 2012 I supervised several Bachelor/Master theses that worked on
adding features to Pyrolog. In the process we added support for Prolog modules,
`DCGs`_, `attributed variables`_, ``freeze`` and ``when``. All these were done by my
excellent students Sven Hager and René Bartelmus. This left the fundamental
execution model intact (with some small additions). I also spent some time
improving the error messages of Pyrolog to for example show backtraces on
Prolog exceptions.

Pyrolog also served as an `early test case`_ for David Schneider's ARM JIT
backend. In January 2011, he could already run Pyrolog microbenchmarks with the
JIT on a BeagleBoard, while the backend still needed debugging before running
more complex Python benchmarks.

.. _`early test case`: /posts/2011/01/jit-backend-for-arm-processors-5994810755839586463.html

In 2012 I mostly wrote my PhD thesis [Bolz2012]_. It contains a chapter on Pyrolog based
on the PPDP 2010 paper. That chapter argues that the fact that Pyrolog works
relatively well demonstrates that the RPython meta-JIT can be used for quite a
wide variety of languages.

There was also another chapter that compared how a meta-tracing JIT works with
more classical partial evaluation approaches. The code of that was again
written in Prolog and originally_ presented_ `here on the blog`_.

.. _originally: /posts/2012/01/simple-tracer-for-flow-graph-language-6930951890987229484.html 
.. _presented: /posts/2012/02/optimizing-traces-of-flow-graph-4169388883059419385.html
.. _`here on the blog`: /posts/2012/02/larger-example-for-flow-graph-language-6139699450091061040.html

At this point I left Düsseldorf. In the winter semester 2012/13 I spent half a
year in Berlin at `Hasso-Plattner-Institute`_ with my PhD co-advisor `Robert
Hirschfeld`_ as a postdoc. In 2013 I started working with `Laurie Tratt`_ at
King's College.

At this point the main Pyrolog story kind of ends. There were only some small
improvements happening in the succeeding years. However, Pyrolog ideas led to
followup research in other projects, and I want to discuss some of them.

2012/2013 Compressed Terms
==========================

One experiment that I had tried to get working in Pyrolog in 2010 and 2011, but
ended up never merging, was compressed terms. The idea comes from the
observation that certain patterns of terms occur repeatedly. For example an
association list has terms of the form ``[A/B|C]`` repeated. Instead of
allocating separate list and pair objects for every entry, the plan was to
share a description of that structure, the "shape", and store each entry's keys
and values in a flat storage data structure. This would make every entry have
less indirection and use fewer words of memory.

However, I had never managed to get that working in Prolog, because variable
bindings can create these patterns after the fact. A field that initially
contained an unbound variable could later refer to a whole structured term, so
the opportunities for compression changed after construction, and again on
backtracking. 

When I was at HPI for six months in winter 2012/2013 I worked with Tobias Pape to
implement the same compression idea for a simpler functional language called
lamb. Tobias pushed this approach much further in the following years
[PBH2015]_, [PBH2017]_. My hope was to eventually understand the problem well
enough to be able to port it back to Pyrolog. But that part never happened. We
did eventually try those ideas in Pycket though.


2013 Unipycation
===================================

In 2013 I started working in London. The goal of our research project there was
"language composition". Edd Barrett, Laurie Tratt and I implemented combined
RPython implementations of PyPy plus another language, with a way to integrate
the two involved languages. The first pair we tried was combining PyPy and
Pyrolog in a project called Unipycation [BBT2013]_. The project made it
possible to call into Prolog from Python and vice versa. The RPython meta-JIT
can optimize across this language boundary and even perform cross-language
inlining. Unfortunately we never found super compelling use-cases for this
combination.

2013 Pycket
==============

Also in 2013 I started working on Pycket_, an RPython implementation of Racket,
together with `Sam Tobin-Hochstadt`_ and `Jeremy Siek`_. Later Tobias Pape and
Spenser Bauman also joined. The Pycket architecture was indirectly inspired by
the Pyrolog continuation approach. We implemented the CEK machine relatively
directly in RPython. This also used a flat host stack and it made implementing
things like ``call/cc`` relatively straightforward [Pycket2015]_.

One of the great new ideas we adopted in Pycket was "false loop filtering",
originally from IBM Research [HWISN2011]_. This takes calling context into
account when tracing function calls and prevents the tracing JIT from
recognizing "false loops", which would never run for more than one iteration. I
always wanted to port this idea back to Pyrolog and implemented a prototype,
but never really polished it enough to be able to merge it.

Another implementation technique in Pycket was to make continuation objects
much smaller, to make the case of them escaping to the heap less bad. This
approach *did* `make it back to Pyrolog`_.

2022-2024 RPython implementation of Effekt
==========================================

I left King's College in 2016 and have been back at Uni Düsseldorf (half-time)
since 2017. In 2022 I started working with `Marcial Gaißert`_ and `Jonathan
Brachthäuser`_ on an RPython implementation of Effekt_ and related languages.
This was an implementation of a JIT for `effect handlers`_ in RPython [GBB2025]_.
Again, it uses the approach of having reified stack frames/continuations which
can then be manipulated by the interpreter, adding effect handlers on top of it.

2026 Git Conversion
================================

This fall, I got an email by a researcher about Pyrolog and realized that it
was 20 years old this year. Subsequently I merged various strands of the
surviving mercurial history into a new `Github repo`_, fixed some bugs and
implemented some convenience features.

.. figure:: /images/2026-pyrolog-screenshot.png
   :width: 80%

   Screenshot of Pyrolog


Conclusion
===========

.. figure:: /images/2026-pyrolog-activity-by-month-authors.svg
   :width: 100%

   commits per month on the main branch, by author

Pyrolog has always been a much more researchy project than PyPy itself. While
PyPy tries to be an open source project and "product", Pyrolog never had any
users and even I never used it for anything beyond small demos, some
research prototypes, and benchmarking. While some quite interesting research
came out of Pyrolog, I think having some real applications running on top of it
would have given me a much more concrete goal to improve it towards.

Implementation wise, Pyrolog inherited some of the problems of PyPy. In PyPy we
were quite strongly focused on peak performance in the first few years, leading
to performance cliffs. Pyrolog also had those in even stronger form, due to the
constant allocations of the interpreter.

Some very interesting interaction between Pyrolog, various Prolog JIT
prototypes and the PyPy/RPython meta-JIT emerged. Pyrolog forced the RPython
JIT to support quite different execution models which made it applicable to
other languages than just object-oriented imperative ones.

I still have no concrete use case for Pyrolog so it's kind of unlikely that I
will work much more on it right now. But my development on this project was
always quite bursty, so I am bound to return to it at some point in the future.

I would like to end with thanking all the contributors and the long line of
Prolog researchers that inspired and encouraged me.


.. _`Logilab`: https://www.logilab.fr/
.. _`Peter van Roy`: https://webperso.info.ucl.ac.be/~pvr/
.. _`Gecode`: https://www.gecode.org/
.. _`Michael Leuschel's`: https://www.cs.hhu.de/en/research-groups/software-engineering-and-programming-languages/our-team/team/michael-leuschel/
.. _`DCGs`: https://www.swi-prolog.org/pldoc/man?section=DCG
.. _`attributed variables`: https://www.swi-prolog.org/pldoc/man?section=attvar
.. _`Hasso-Plattner-Institute`: https://hpi.de/
.. _`Robert Hirschfeld`: https://hirschfeld.org/
.. _`Laurie Tratt`: https://tratt.net/laurie/
.. _`Sam Tobin-Hochstadt`: https://samth.github.io/
.. _`Jeremy Siek`: https://luddy.iu.edu/people/siek-jeremy.html
.. _`Marcial Gaißert`: https://pl.cs.uni-tuebingen.de/team/gaissert/
.. _`Jonathan Brachthäuser`: https://b-studios.de/about
.. _`pyrepl`: https://github.com/pypy/pyrepl
.. _`SWI`: https://www.swi-prolog.org/
.. _`Sicstus Prolog`: https://sicstus.sics.se/
.. _`Github repo`: https://github.com/cfbolz/pyrolog
.. _`first surviving commit`: https://github.com/cfbolz/pyrolog/commit/6653a22
.. _`changed the variable representation`: https://github.com/cfbolz/pyrolog/commit/04307d2
.. _Pycket: https://github.com/pycket/pycket
.. _Effekt: https://effekt-lang.org/
.. _`effect handlers`: https://effekt-lang.org/docs/concepts/effect-handlers
.. _pyjitpl5: https://github.com/pypy/pypy/commit/bbb1996550b
.. _`reified RPython objects`: https://github.com/cfbolz/pyrolog/commit/fc1a4f9
.. _`implementing support for cyclic term unification`: https://github.com/cfbolz/pyrolog/commit/8d51938
.. _`make it back to Pyrolog`: https://github.com/cfbolz/pyrolog/commit/59fb825


Bibliography
============


.. [TB1990] P. Tarau, M. Boyer.
   *Elementary logic programs*. PLILP 1990, LNCS 456, pp. 159–173.
   `DOI <https://doi.org/10.1007/BFb0024183>`__.

.. [Tarau1992] Paul Tarau.
   *BinProlog: a continuation passing style Prolog engine*.
   PLILP 1992, LNCS 631, pp. 479–480. Poster.

.. [SS1994] Leon S. Sterling, Ehud Y. Shapiro.
   *The Art of Prolog: Advanced Programming Techniques*.
   2nd edition, MIT Press, 1994.
   `Publisher page <https://mitpress.mit.edu/9780262691635/the-art-of-prolog/>`__.

.. [Lindgren1994] Thomas Lindgren.
   *A Continuation-Passing Style for Prolog*.
   International Logic Programming Symposium, 1994, pp. 603–617.

.. [VanRoy1994] Peter Van Roy.
   *1983–1993: The Wonder Years of Sequential Prolog Implementation*.
   Journal of Logic Programming 19–20, 1994, pp. 385–441.
   `DOI <https://doi.org/10.1016/0743-1066(94)90031-0>`__;
   `author-hosted technical report PDF <https://webperso.info.ucl.ac.be/~pvr/PRL-TR-36.pdf>`__
   (DEC Paris Research Laboratory report 36, December 1993).

.. [Neumerkel1995] Ulrich Neumerkel.
   *Continuation Prolog: A new intermediary language for WAM and BinWAM
   code generation*. Post-ILPS 1995 Workshop on Implementation of Logic
   Programming Languages, 1995.
   `PDF <https://www.complang.tuwien.ac.at/ulrich/papers/PDF/contp95.pdf>`__.

.. [CM2003] William F. Clocksin, Christopher S. Mellish.
   *Programming in Prolog: Using the ISO Standard*.
   5th edition, Springer, 2003.
   `DOI <https://doi.org/10.1007/978-3-642-55481-0>`__.

.. [VH2004] Peter Van Roy, Seif Haridi.
   *Concepts, Techniques, and Models of Computer Programming*.
   MIT Press, 2004. ISBN 9780262220699.
   `Publisher page <https://mitpress.mit.edu/9780262220699/concepts-techniques-and-models-of-computer-programming/>`__;
   `author's book page <https://webperso.info.ucl.ac.be/~pvr/book.html>`__.

.. [BD2004] Dariusz Biernacki, Olivier Danvy.
   *From Interpreter to Logic Engine by Defunctionalization*.
   LOPSTR 2003, revised selected papers, published 2004, pp. 143–159.
   `DOI <https://doi.org/10.1007/978-3-540-25938-1_13>`__,
   `PDF <https://ii.uni.wroc.pl/~dabi/publications/LOPSTR03/biernacki-danvy-lopstr03.pdf>`__.

.. [BR2007D071] CF Bolz, Armin Rigo.
   *Support for massive parallelism, optimisation results, practical
   usages and approaches for translation aspects*.
   PyPy Consortium, EU deliverable D07.1, 28 February 2007.
   Listed by PyPy as *Massive Parallelism and Translation Aspects*.
   `Official report index <https://doc.pypy.org/index-report.html>`__;
   `report PDF <https://foss.heptapod.net/pypy/extradoc/-/blob/branch/extradoc/eu-report/D07.1_Massive_Parallelism_and_Translation_Aspects-2007-02-28.pdf>`__.

.. [Bolz2007] CF Bolz.
   *A Prolog Interpreter in Python*. Bachelor thesis,
   Heinrich Heine University Düsseldorf, 2007.
   `PDF <https://cfbolz.de/Bolz2007-Bachelorarbeit.pdf>`__.

.. [BLR2010] CF Bolz, Michael Leuschel, Armin Rigo.
   *Towards Just-In-Time Partial Evaluation of Prolog*.
   LOPSTR 2009, revised selected papers, LNCS 6037, 2010, pp. 158–172.
   `DOI <https://doi.org/10.1007/978-3-642-12592-8_12>`__;
   `author manuscript <https://stups.hhu-hosting.de/downloads/pdf/BoLeRi09_235.pdf>`__.

.. [BLS2010] CF Bolz, Michael Leuschel, David Schneider.
   *Towards a Jitting VM for Prolog Execution*. PPDP 2010, pp. 99–108.
   `DOI <https://doi.org/10.1145/1836089.1836102>`__;
   `author manuscript <https://stups.hhu-hosting.de/downloads/pdf/BoLeSch2010.pdf>`__.

.. [HWISN2011] Hiroshige Hayashizaki, Peng Wu, Hiroshi Inoue,
   Mauricio J. Serrano, Toshio Nakatani.
   *Improving the Performance of Trace-based Systems by False Loop Filtering*.
   ASPLOS XVI, 2011, pp. 405–418.
   `DOI <https://doi.org/10.1145/1950365.1950412>`__;
   `IBM Research publication page <https://research.ibm.com/publications/improving-the-performance-of-trace-based-systems-by-false-loop-filtering>`__.

.. [Bolz2012] CF Bolz.
   *Meta-Tracing Just-in-Time Compilation for RPython*.
   PhD thesis, Heinrich-Heine-Universität Düsseldorf, September 2012.
   `Author's thesis page <https://cfbolz.de/phdthesis/>`__;
   `PDF <https://cfbolz.de/stuff/cfbolz-meta-tracing.pdf>`__;
   `university repository <https://docserv.uni-duesseldorf.de/servlets/DocumentServlet?id=30464>`__.

.. [BBT2013] Edd Barrett, CF Bolz, Laurence Tratt.
   *Unipycation: A Case Study in Cross-Language Tracing*.
   VMIL 2013, pp. 31–40.
   `DOI <https://doi.org/10.1145/2542142.2542146>`__;
   `author manuscript <https://tratt.net/laurie/research/pubs/papers/barrett_bolz_tratt__unipycation_a_study_in_cross_language_tracing.pdf>`__.

.. [Pycket2015] Spenser Bauman, CF Bolz, Robert Hirschfeld,
   Vasily Kirilichev, Tobias Pape, Jeremy G. Siek, Sam Tobin-Hochstadt.
   *Pycket: A Tracing JIT for a Functional Language*.
   ICFP 2015, pp. 22–34.
   `DOI <https://doi.org/10.1145/2784731.2784740>`__;
   `author manuscript <https://soft-dev.org/pubs/pdf/bauman_bolz_hirschfeld_kirilichev_pape_siek_tobin_hochstadt__pycket_a_tracing_jit_for_a_functional_language.pdf>`__.

.. [PBH2015] Tobias Pape, CF Bolz, Robert Hirschfeld.
   *Adaptive Just-in-time Value Class Optimization: Transparent Data
   Structure Inlining for Fast Execution*. SAC 2015.
   `DOI <https://doi.org/10.1145/2695664.2695837>`__;
   `PDF <https://www.hirschfeld.org/writings/media/PapeBolzHirschfeld_2015_AdaptiveJustInTimeValueClassOptimization_AcmDL.pdf>`__.

.. [PBH2017] Tobias Pape, CF Bolz, Robert Hirschfeld.
   *Adaptive just-in-time value class optimization for lowering memory
   consumption and improving execution time performance*.
   Science of Computer Programming 140, 2017, pp. 17–29.
   Published online in 2016.
   `DOI <https://doi.org/10.1016/j.scico.2016.08.003>`__;
   `PDF <https://www.hirschfeld.org/writings/media/PapeBolzHirschfeld_2017_AdaptiveJustInTimeValueClassOptimizationForLoweringMemoryConsumptionAndImprovingExecutionTimePerformance_Elsevier.pdf>`__.

.. [GBB2025] Marcial Gaißert, CF Bolz-Tereick,
   Jonathan Immanuel Brachthäuser.
   *Tracing Just-in-Time Compilation for Effects and Handlers*.
   Proceedings of the ACM on Programming Languages 9 (OOPSLA2),
   Article 307, October 2025.
   `DOI <https://doi.org/10.1145/3763085>`__;
   `author publication page <https://pl.cs.uni-tuebingen.de/publications/gaissert2025tracing/>`__;
   `technical report <https://pl.cs.uni-tuebingen.de/publications/gaissert2025tracing.pdf>`__.


