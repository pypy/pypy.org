.. title: Natural Language Processing for Icelandic with PyPy: A Case Study
.. slug: nlp-icelandic-case-study
.. date: 2022-02-06 15:00:00 UTC
.. tags: casestudy
.. category: 
.. link: 
.. description: 
.. type: rest
.. author: Vilhjálmur Þorsteinsson

====================================================================
Natural Language Processing for Icelandic with PyPy: A Case Study
====================================================================

`Icelandic <https://en.wikipedia.org/wiki/Icelandic_language>`__ is one
of the smallest languages of the world, with about 370.000 speakers. It
is a language in the Germanic family, most similar to Norwegian, Danish
and Swedish, but closer to the original `Old
Norse <https://en.wikipedia.org/wiki/Old_Norse>`__ spoken throughout
Scandinavia until about the 14th century CE.

As with other small languages, there are `worries that the language may
not
survive <https://www.theguardian.com/world/2018/feb/26/icelandic-language-battles-threat-of-digital-extinction>`__
in a digital world, where all kinds of fancy applications are developed
first - and perhaps only - for the major languages. Voice assistants,
chatbots, spelling and grammar checking utilities, machine translation,
etc., are increasingly becoming staples of our personal and professional
lives, but if they don’t exist for Icelandic, Icelanders will gravitate
towards English or other languages where such tools are readily
available.

Iceland is a technology-savvy country, with `world-leading adoption
rates of the
Internet <https://ourworldindata.org/grapher/share-of-individuals-using-the-internet?tab=table>`__,
PCs and smart devices, and a thriving software industry. So the
government figured that it would be worthwhile to fund a `5-year
plan <https://aclanthology.org/2020.lrec-1.418.pdf>`__ to build natural
language processing (NLP) resources and other infrastructure for the
Icelandic language. The project focuses on collecting data and
developing open source software for a range of core applications, such
as tokenization, vocabulary lookup, n-gram statistics, part-of-speech
tagging, named entity recognition, spelling and grammar checking, neural
language models and speech processing.

------------

My name is Vilhjálmur Þorsteinsson, and I’m the founder and CEO of a
software startup `Miðeind <https://mideind.is/english.html>`__ in Reykjavík,
Iceland, that employs 10 software engineers and linguists and focuses on
NLP and AI for the Icelandic language. The company participates in the
government’s language technology program, and has contributed
significantly to the program’s core tools (e.g., a tokenizer and a
parser), spelling and grammar checking modules, and a neural machine
translation stack.

When it came to a choice of programming languages and development tools
for the government program, the requirements were for a major, well
supported, vendor-and-OS-agnostic FOSS platform with a large and diverse
community, including in the NLP space. The decision to select Python as
a foundational language for the project was a relatively easy one. That
said, there was a bit of trepidation around the well known fact that
CPython can be slow for inner-core tasks, such as tokenization and
parsing, that can see heavy workloads in production.

I first became aware of PyPy in early 2016 when I was developing a
crossword game `Netskrafl <https://github.com/mideind/Netskrafl>`__ in Python 2.7
for Google App Engine. I had a utility program that compressed a
dictionary into a Directed Acyclic Word Graph and was taking 160
seconds  to run on CPython 2.7, so I tried PyPy and to my amazement saw
a 4x speedup (down to 38 seconds), with literally no effort besides
downloading the PyPy runtime.

This led me to select PyPy as the default Python interpreter for my
company’s Python development efforts as well as for our production
websites and API servers, a role in which it remains to this day. We
have followed PyPy’s upgrades along the way, being just about to migrate
our minimally required language version from 3.6 to 3.7.

In NLP, speed and memory requirements can be quite important for
software usability. On the other hand, NLP logic and algorithms are
often complex and challenging to program, so programmer productivity and
code clarity are also critical success factors. A pragmatic approach
balances these factors, avoids premature optimization and seeks a
careful compromise between maximal run-time efficiency and minimal
programming and maintenance effort.

Turning to our use cases, our Icelandic text
tokenizer `"Tokenizer" <https://github.com/mideind/Tokenizer>`__ is fairly light,
runs tight loops and performs a large number of small, repetitive
operations. It runs very well on PyPy’s JIT and has not required further
optimization.

Our `Icelandic parser <https://github.com/mideind/GreynirPackage>`__ is,
if I may say so myself, a piece of work. It `parses natural language
text <https://aclanthology.org/R19-1160.pdf>`__ according to a
`hand-written context-free
grammar <https://github.com/mideind/GreynirPackage/blob/master/src/reynir/Greynir.grammar>`__,
using an `Earley-type
algorithm <https://en.wikipedia.org/wiki/Earley_parser>`__ as `enhanced
by Scott and
Johnstone <https://www.sciencedirect.com/science/article/pii/S0167642309000951>`__.
The CFG contains almost 7,000 nonterminals and 6,000 terminals, and the
parser handles ambiguity as well as left, right and middle recursion. It
returns a packed parse forest for each input sentence, which is then
pruned by a scoring heuristic down to a single best result tree.

This parser was originally coded in pure Python and turned out to be
unusably slow when run on CPython - but usable on PyPy, where it was
3-4x faster. However, when we started applying it to heavier production
workloads, it  became apparent that it needed to be faster still. We
then proceeded to convert the innermost Earley parsing loop from Python
to `tight
C++ <https://github.com/mideind/GreynirPackage/blob/master/src/reynir/eparser.cpp>`__
and to call it from PyPy via
`CFFI <https://cffi.readthedocs.io/en/latest/>`__, with callbacks for
token-terminal matching functions (“business logic”) that remained on
the Python side. This made the parser much faster (on the order of 100x
faster than the original on CPython) and quick enough for our production
use cases.

Connecting C++ code with PyPy proved to be quite painless using CFFI,
although we had to figure out a few `magic incantations in our build
module <https://github.com/mideind/GreynirPackage/blob/master/src/reynir/eparser_build.py>`__
to make it compile smoothly during setup from source on Windows and
MacOS in addition to Linux. Of course, we build binary PyPy and CPython
wheels for the most common targets so most users don’t have to worry
about setup requirements.

With the positive experience from the parser project, we proceeded to
take a similar approach for two other core NLP packages: our compressed
vocabulary package `BinPackage <https://github.com/mideind/BinPackage>`__ 
(known on PyPI as `islenska <https://pypi.org/project/islenska/>`__ and our
trigrams database package `Icegrams <https://github.com/mideind/Icegrams>`__.
These packages both take large text input (3.1 million word forms with
inflection data in the vocabulary case; 100 million tokens in the
trigrams case) and compress it into packed binary structures. These
structures are then memory-mapped at run-time using
`mmap <https://docs.python.org/3/library/mmap.html>`__ and queried via
Python functions with a lookup time in the microseconds range. The
low-level data structure navigation is `done in
C++ <https://github.com/mideind/Icegrams/blob/master/src/icegrams/trie.cpp>`__,
called from Python via CFFI. The ex-ante preparation, packing,
bit-fiddling and data structure generation is fast enough with PyPy, so
we haven’t seen a need to optimize that part further.

To showcase our tools, we host public (and open source) websites such as
`greynir.is <https://greynir.is/>`__ for our parsing, named entity
recognition and query stack and
`yfirlestur.is <https://yfirlestur.is/>`__ for our spell and grammar
checking stack. The server code on these sites is all Python running on
PyPy using `Flask <https://flask.palletsprojects.com/en/2.0.x/>`__,
wrapped in `gunicorn <https://gunicorn.org/>`__ and hosted on
`nginx <https://www.nginx.com/>`__. The underlying database is
`PostgreSQL <https://www.postgresql.org/>`__ accessed via
`SQLAlchemy <https://www.sqlalchemy.org/>`__ and
`psycopg2cffi <https://pypi.org/project/psycopg2cffi/>`__. This setup
has served us well for 6 years and counting, being fast, reliable and
having helpful and supporting communities.

As can be inferred from the above, we are avid fans of PyPy and
commensurately thankful for the great work by the PyPy team over the
years. PyPy has enabled us to use Python for a larger part of our
toolset than CPython alone would have supported, and its smooth
integration with C/C++ through CFFI has helped us attain a better
tradeoff between performance and programmer productivity in our
projects. We wish for PyPy a great and bright future and also look
forward to exciting related developments on the horizon, such as
`HPy <https://hpyproject.org/>`__.
