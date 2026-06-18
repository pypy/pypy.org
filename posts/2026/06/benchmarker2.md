<!--
.. title: A new benchmark runner for PyPy
.. slug: benchmarker2-for-pypy
.. date: 2026-06-14 15:07:09 UTC
.. tags: performance, benchmarks, infrastructure
.. category:
.. link:
.. description:
.. type: text
.. author: mattip
-->


The [https://speed.pypy.org](https://speed.pypy.org) site has been running the [PyPy benchmark
suite](https://foss.heptapod.net/pypy/benchmarks) since 2010. Our
first benchmarking machine was called tannit, and it faithfully ran the suite
from May 2010 to Dec 2016. For a brief period in the middle we had a machine
called speed-python, but tannit was the gold standard. In June 2016 we started
running benchmarks on our current machine, __benchmarker__ (Intel i7-7700). It has been graciously
sponsored by [Baroque Software](https://baroquesoftware.com/). Based on an Ubuntu xenial
chroot, the machine has been quite stable but over the years has had a few
kernel exploits blocked in firmware that changed its base performance.

It is time to update. Rather than use the same machine with updated software,
we decided to opt for different hardware. Since the beginning of May we have been
running the benchmark suite on __benchmarker2__: an AMD Ryzen 5 3600 machine. In
order to try to stabilize benchmarks the machine was set up:

- without SMT (hyper-threading)
- using `cpuset` to partition CPUs 3,4,5 off (the CPU has 2 CCD chiplets so the
  CPU sets are truly independent, the reason we chose the Zen2 architecture)
  and use them exclusively for benchmarking
- disable turbo speed strategy.

It runs debian13 as a base operating system, and the benchmarks run in a
`manylinux2_28` docker, which provides gcc14.

In order to establish a baseline, I compiled CPython 3.11.5 with:
```
./configure --prefix=/opt/cpython-3.11 --enable-optimizations \
--with-computed-gotos --enable-shared LDFLAGS='-Wl,-rpath,\$$ORIGIN/../lib'
```

The difference between the two machines is striking: where the xenial image
(with GCC 5.4) benchmark comparison to CPython 3.11.9 shows a 3x improvement
when run on PyPy on benchmarker, the newer machine with the newer compiler and
a fresh baseline shows a 4.3x improvement.  I can only speculate that the major
differences between the results is:

- The CPython 3.11.9 run was done in June 2024. This was before some firmware
  kernel changes applied to the host machine that slowed it down. I did notice
  at the time the exploit migitagion firmware was applied that the overall
  comparison dropped from 3.3x to 3x, but felt the additional protection was
  warrented.
- The newer software image uses GCC 14, where the older one used GCC 5.
- The AMD machine has 32MB of L3 cache, the Intel machine has 8MB.
- The AMD machine uses RAM at 3200MHz, the Intel at 2400MHz.

The last 3 points may affect PyPy more than CPython, since PyPy's JIT is more
memory intensive and the RPython codegen may be handled better by newer compilers.

This is the first step in an overhaul of PyPy's infrastructure. Other plans in
the pipeline:

- Move all the buildbot builds from `manylinux_2014` to `manylinux2_28`-based
  images. This will match the move on benchmarker2. It will require some
  adaptations so that tests will pass on the newer compiler, see
  [pypy/pypy#5488](https://github.com/pypy/pypy/pull/5488). This will mean an ABI break,
  so the next PyPy release will leave behind the 7.3.x series.
- Think about [updating our use of buildbot 0.8.8](https://github.com/pypy/buildbot/issues/1),
  which is woefully out of date. Since we have a heavily customized [summary
  page](https://buildbot.pypy.org/summary?branch=py3.11), and the twistd-based
  endpoints are not supported on buildbot 0.9 and up, we set up a
  [build-summary](https://build-summary.pypy.org/summary?branch=py3.11)
  alternative that is synchronized to the buildbot work.
- Perhaps make more use of the free GitHub actions workers to replace or
  enhance the buildbot workers. Some of that can be seen in PR 5488. The
  build-summary service is also able to ingest github action testing results.
- Continue to push on in CPython compatibility, performance improvements, and
  bugfixes, as well as work on a [PyPy 3.12
  version](https://github.com/pypy/pypy/issues?q=is%3Aissue%20state%3Aopen%20milestone%3A%22Python%203.12%22)

Help of course is welcome.

Matti
