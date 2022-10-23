.. title: The PyPy Blog Turns 15 Years
.. slug: blog-15-years
.. date: 2022-10-30 12:00:00 UTC
.. tags: meta
.. category:
.. link:
.. description:
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

Exactly 15 years ago today we wrote the `first blog post on the PyPy blog`_!
Over the years, we have written 423 posts, from the `shortest`_ to the
`longest`_. In 2021 we moved_ from blogger_ to our own domain.

.. _`first blog post on the PyPy blog`: /posts/2007/10/first-post-8150793557471983289.html
.. _`shortest`: /posts/2007/12/faster-than-c-8057790636822502084.html
.. _`longest`: /posts/2022/07/toy-optimizer.html
.. _moved: /posts/2021/03/pypys-blog-has-moved.html
.. _blogger: https://morepypy.blogspot.com

The topics over the years varied widely, we published release_ announcements_;
roadmaps_; JIT_, GC_ and STM_ updates_; benchmarks_; sprint_, trip_ and
conference_ reports_; technical_ deep_ dives_; `case studies`_; april_ `fool's
jokes`_; research_ projects; other_ languages_ using_ RPython; finished PhD_
Bachelor_ and Master_, theses_; pictures:

.. image:: /images/2022-pypy-pictures-collage-small.jpg
   :alt: a collage of photos taken at PyPy sprints
   :target: /images/2022-pypy-pictures-collage.jpg

and diagrams:

.. image:: /images/2022-pypy-diagrams-collage-small.png
   :alt: a collage of diagrams from previous blog posts
   :target: /images/2022-pypy-diagrams-collage.png


.. _release: /posts/2013/05/pypy-20-einstein-sandwich-635158782365435530.html
.. _announcements: /posts/2017/06/pypy-v58-released-739876359584854017.html
.. _roadmaps: /posts/2009/04/roadmap-for-jit-377358891902851723.html
.. _JIT: /posts/2010/06/blackhole-interpreter-2752965445510091289.html
.. _GC: /posts/2013/10/incremental-garbage-collector-in-pypy-8956893523842234676.html
.. _STM: /posts/2013/10/update-on-stm-7145890443443707910.html
.. _updates: /posts/2019/07/pypy-jit-for-aarch64-7161523403247118006.html
.. _benchmarks: /posts/2018/06/repeating-matrix-multiplication-8641748742577945875.html
.. _sprint: /posts/2008/10/dsseldorf-sprint-report-days-1-3-5256639868851086032.html
.. _trip: /posts/2007/11/pypy-road-show-1-new-york-and-ibm-7837076523877011699.html
.. _conference: /posts/2009/07/ecoop-2009-8415055006373020774.html
.. _reports: /posts/2012/04/pycon-2012-wrap-up-559575896040055505.html
.. _technical: /posts/2016/07/reverse-debugging-for-python-8854823774141612670.html
.. _deep: /posts/2010/11/efficiently-implementing-python-objects-3838329944323946932.html
.. _dives: /posts/2015/10/pypy-memory-and-warmup-improvements-2-4598780879518640015.html
.. _`case studies`: /posts/2022/02/nlp-icelandic-case-study.html
.. _april: /posts/2008/04/trying-to-get-pypy-to-run-on-python-30-5082015544752137606.html
.. _`fool's jokes`: /posts/2008/04/other-aprils-fools-ideas-955926452383759016.html
.. _research: /posts/2015/03/pydgin-using-rpython-to-generate-fast-1514065178985838697.html
.. _PhD: /posts/2010/10/phd-thesis-about-pypys-cli-jit-backend-969267841095296323.html
.. _Bachelor: /posts/2019/04/an-rpython-jit-for-lpegs-4779548053359386284.html
.. _Master: /posts/2008/10/prolog-jit-masters-thesis-finished-5462132148241449867.html
.. _theses: /posts/2019/04/an-rpython-jit-for-lpegs-4779548053359386284.html
.. _other: /posts/2013/02/announcing-topaz-rpython-powered-ruby-6662407703061538341.html
.. _languages: /posts/2012/07/hello-everyone-6869934374873967346.html
.. _using: /posts/2014/08/a-field-test-of-software-transactional-5659022209916605798.html
.. _RPython: /posts/2015/02/experiments-in-pyrlang-with-rpython-8103387814587972227.html

Quite a number of blog posts were very early iterations of papers that we
published later, here are a few that I can remember:

- `Applying a Tracing JIT to an Interpreter`_ became `Tracing the meta-level:
  PyPy's tracing JIT compiler`_ at ICOOOLPS 2009, by far our most successful
  paper.

- `Escape Analysis in PyPy's JIT`_ became `Allocation removal by partial
  evaluation in a tracing JIT`_ at PEPM 2010.

- `Controlling the Tracing of an Interpreter With Hints`_ was a draft of the
  paper `Runtime feedback in a meta-tracing JIT for efficient dynamic
  languages`_ at ICOOOLPS 2011

- `Using Escape Analysis Across Loop Boundaries for Specialization`_ was the
  nucleus of `Loop-aware optimizations in PyPy's tracing JIT`_ at DLS 2012.

- `List Strategies`_ was eventually turned into the paper `Storage strategies
  for collections in dynamically typed languages`_ at OOPSLA 2013.


.. _`Applying a Tracing JIT to an Interpreter`: /posts/2009/03/applying-tracing-jit-to-interpreter-3287844903778799266.html
.. _`Tracing the meta-level: PyPy's tracing JIT compiler`: https://dl.acm.org/doi/10.1145/1565824.1565827

.. _`Escape Analysis in PyPy's JIT`: /posts/2010/09/escape-analysis-in-pypys-jit-1780048403046080197.html
.. _`Allocation removal by partial evaluation in a tracing JIT`: https://dl.acm.org/doi/10.1145/1929501.1929508

.. _`Controlling the Tracing of an Interpreter With Hints`: /posts/2011/03/controlling-tracing-of-interpreter-with_21-6524148550848694588.html
.. _`Runtime feedback in a meta-tracing JIT for efficient dynamic languages`: https://dl.acm.org/doi/10.1145/2069172.2069181

.. _`Using Escape Analysis Across Loop Boundaries for Specialization`: /posts/2010/09/using-escape-analysis-across-loop-2887031293132023676.html
.. _`Loop-aware optimizations in PyPy's tracing JIT`: https://dl.acm.org/doi/10.1145/2384577.2384586

.. _`List Strategies`: /posts/2011/10/more-compact-lists-with-list-strategies-8229304944653956829.html
.. _`Storage strategies for collections in dynamically typed languages`: https://dl.acm.org/doi/10.1145/2509136.2509531



In terms of visitors, the top five posts on the old blog were – on the new blog
we simply don't have stats (yet?):

1. `Let's remove the global interpreter lock`_
2. `Tutorial: Writing an Interpreter with PyPy, Part 1`_
3. `PyPy's new JSON parser`_
4. `PyPy gets funding from Mozilla for Python 3.5 support`_
5. `How to make your code 80 times faster`_

.. _`Let's remove the global interpreter lock`: /posts/2017/08/lets-remove-global-interpreter-lock-748023554216649595.html
.. _`Tutorial: Writing an Interpreter with PyPy, Part 1`: /posts/2011/04/tutorial-writing-interpreter-with-pypy-3785910476193156295.html
.. _`PyPy's new JSON parser`: /posts/2019/10/pypys-new-json-parser-492911724084305501.html
.. _`PyPy gets funding from Mozilla for Python 3.5 support`: /posts/2016/08/pypy-gets-funding-from-mozilla-for-5569307998787871200.html
.. _`How to make your code 80 times faster`: /posts/2017/10/how-to-make-your-code-80-times-faster-1424098117108093942.html 


The number of posts per year developed like this:

.. image:: /images/2022-pypy-posts-per-year.svg

While looking through the posts, there were a few that stood out to me in some
way, so here's a subjective list of ones that I had fun looking at again:

- 2008: `Sprint Discussions: JIT Generator Planning`__
- 2009: `PyPy gets a new compiler`__
- 2010: `Oh, and btw: PyPy gets funding through "Eurostars"`__ 
- 2011: `Realtime image processing in Python`__
- 2012: `Architecture of Cppyy`__
- 2013: `10 years of PyPy`__
- 2014: `PyPy IO Improvements`__
- 2015: `Automatic SIMD vectorization support in PyPy`__
- 2016: `PyPy Enterprise Edition`__
- 2017: `Async HTTP benchmarks on PyPy3`__ 
- 2018: `Improving SyntaxError in PyPy`__
- 2018: `The First 15 Years of PyPy — a Personal Retrospective`__
- 2019: `PyPy for low-latency systems`__
- 2020: `PyPy and CFFI have moved to Heptapod`__
- 2021: `Some Ways that PyPy uses Graphviz`__

.. __: /posts/2008/10/sprint-discussions-jit-generator-3301578822967655604.html
.. __: /posts/2009/08/pypy-gets-new-compiler_25-6401910947439531107.html
.. __: /posts/2010/12/oh-and-btw-pypy-gets-funding-through-3568486750776147382.html
.. __: /posts/2011/07/realtime-image-processing-in-python-6985924592886873374.html
.. __: /posts/2012/06/architecture-of-cppyy-9077100041707701102.html
.. __: /posts/2013/02/10-years-of-pypy-634401291726575821.html
.. __: /posts/2014/11/pypy-io-improvements-1042070332447047674.html
.. __: /posts/2015/10/automatic-simd-vectorization-support-in-639063580401330508.html
.. __: /posts/2016/04/pypy-enterprise-edition-3688275697656890948.html
.. __: /posts/2017/03/async-http-benchmarks-on-pypy3-1092124994927894138.html
.. __: /posts/2018/04/improving-syntaxerror-in-pypy-5733639208090522433.html
.. __: /posts/2018/09/the-first-15-years-of-pypy-3412615975376972020.html#incentives-of-oss-compared-to-academia
.. __: /posts/2019/01/pypy-for-low-latency-systems-613165393301401965.html
.. __: /posts/2020/02/pypy-and-cffi-have-moved-to-heptapod-5791595152472747032.html
.. __: /posts/2021/04/ways-pypy-graphviz.html

We'd like to thank our authors, guest authors, commenters, users and readers who
have stuck with us through one and a half decades! If there's any particular
topics you would like to read something about, or any guest posts you'd like to
write, let us know!
