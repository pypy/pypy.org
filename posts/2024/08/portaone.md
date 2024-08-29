<!--
.. title: Guest Post: How PortaOne uses PyPy for high-performance processing, connecting over 1B of phone calls every month
.. slug: portaone
.. date: 2024-08-29 09:00:00 UTC
.. tags: casestudy, guestpost
.. category:
.. link:
.. description:
.. type: text
.. author:
-->


The PyPy project is always happy to hear about industrial use  and deployments
of PyPy. For the [GC bug
finding](https://www.pypy.org/posts/2024/03/fixing-bug-incremental-gc.html)
task earlier this year, we collaborated with PortaOne and we're super happy
that Serhii Titov, head of the QA department at PortaOne, was up to writing
this guest post to describe their use and experience with the project.

-----

## What does PortaOne do?

We at [PortaOne Inc.](https://www.portaone.com/) allow telecom operators to
launch new services (or provide existing services more efficiently) using our
VoIP platform (PortaSIP) and our real-time charging system (PortaBilling),
which provides additional features for cloud PBX, such as call transfer,
queues, interactive voice response (IVR) and more. At this moment our support
team manages several thousand servers with our software installed in 100
countries, through which over 500 telecommunication service providers connect
millions of end users every day. The unique thing about PortaOne is that we
supply the source code of our product to our customers - something unheard of
in the telecom world! Thus we attract "telco innovators", who use our APIs to
build around the system and the source code to create unique tweaks of
functionality, which produces amazing products.

At the core of PortaSIP is the middle-ware component (the proper name for it is
"B2BUA", but that probably does not say much to anyone outside of experts in
VoIP), which implements the actual handling of SIP calls, messages, etc. and
all added features (for instance, trying to send a call via telco operators
through which the cost per minute is lower). It has to be fast (since even a
small delay in establishing a call is noticed by a customer), reliable
(everyone hates when a call drops or cannot be completed) and yet easily
expandable with new functionality. This is why we decided to use Python as
opposed to C/C++ or similar programming languages, which are often used in
telecom equipment.


The B2BUA component is a batch of similar Python processes that are looped
inside a
[`asyncore.dispatcher`](https://docs.python.org/3.10/library/asyncore.html)
wrapper. The load balancing between these Python processes is done by our
stateless SIP proxy server written in C++. All our sockets are served by this
B2BUA. We have our custom client-wrappers around `pymysql`, `redis`,
`cassandra-driver` and `requests` to communicate with external services. Some
of the Python processes use [`cffi`](https://cffi.readthedocs.io/en/stable/)
wrappers around C-code to improve their performance (examples: an Oracle DB
driver, a client to a radius server, a custom C logger).

The I/O operations that block the main thread of the Python processes are
processed in sub-threads. We have custom wrappers  around `threading.Thread`
and also `asyncore.dispatcher`. The results of such operations are returned to
the main thread.

## Improving our performance with PyPy

We started with CPython and then in 2014 switched to PyPy because it was
faster. Here's an exact quote from our first testing notes: "PyPy gives
significant performance boost, ~50%". Nowadays, after years of changes in all
the software involved, PyPy still gives us +50% boost compared to CPython.

Taking care of real time traffic for so many people around the globe is
something we're really proud of. I hope the PyPy team can be proud of it as
well, as the PyPy product is a part of this solution.

## Finding a garbage collector bug: stage 1, the GC hooks

However our path with PyPy wasn't perfectly smooth. There were very rare cases
of crashes on PyPy that we weren't able to catch. That's because to make
coredump useful we needed to switch to PyPy with debug, but we cannot let it
run in that mode on a production system for an extended period of time, and we
did not have any STR (steps-to-reproduce) to make PyPy crash again in our lab.
That's why we kept (and still keep) both interpreters installed just in case,
and we would switch to CPython if we noticed it happening.

At the time of updating PyPy from 3.5 to 3.6 our QA started noticing those
crashes more often, but we still had no luck with STR or collecting proper
coredumps with debug symbols. Then it became even worse after our development
played with the [Garbage Collector's
options](https://doc.pypy.org/en/latest/gc_info.html) to increase performance
of our middleware component. The crashes started to affect our regular
performance testing (controlled by QA manager Yevhenii Bovda). At that point it
was decided that we can no longer live like that and so we started an intense
investigation.

During the first stage of our investigation (following the best practice of
troubleshooting) we narrowed down the issue as much as we could. So, it was not
our code, it was definitely somewhere in PyPy. Eventually our SIP software
engineer [Yevhenii Yatchenko](https://github.com/Yevhenii-Yatchenko) found out
that this bug is connected with the use of our [custom hooks in the
GC](https://doc.pypy.org/en/latest/gc_info.html#gc-hooks). Yevhenii created
ticket [#4899](https://github.com/pypy/pypy/issues/4899) and within 2-3 days we
got a fix from a [member of the PyPy team](https://github.com/cfbolz), in true open-source fashion.

## Finding a garbage collector bug: stage 2, the real bug

Then came stage 2. In parallel with the previous ticket, Yevhenii created
[#4900](https://github.com/pypy/pypy/issues/4900) that we still see failing
with coredumps quite often, and they are not connected to GC custom hooks. In a
nutshell, it took us dozens of back and forward emails, three Zoom sessions and
four versions of a patch to solve the issue. During the last iteration we got a
new set of options to try and a new version of the patch. Surprisingly, that
helped! What a relief! So, the next logical step was to remove all debug
options and run PyPy only with the patch. Unfortunately, it started to fail
again and we came to the obvious conclusion that what will help us is not a
patch, but one of options we were testing out. At that point we found out that
[`PYPY_GC_MAX_PINNED=0`](https://doc.pypy.org/en/latest/gc_info.html#environment-variables)
is a necessary and sufficient condition to solve our issue. This points to
another bug in the garbage collector, somehow related to object pinning.

Here's our current state: we have to add `PYPY_GC_MAX_PINNED=0`, but we do not
face the crashes anymore.

## Conclusion and next steps

Gratitude is extended to Carl for his invaluable assistance in resolving the
nasty bugss, because it seems we're the only ones who suffered from the last
one and we really did not want to fall back to CPython due to its performance
disadvantage.

Serhii Titov, head of the QA department at PortaOne Inc.

P.S. If you are a perfectionist and at this point you have mixed feelings and
you are still bothered by the question "But there might still be a bug in the
GC, what about that?" - Carl has some ideas about it and he will sort it out
(we will help with the testing/verification part).
