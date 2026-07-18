<!--
.. title: Moving linux builds to GLIBC==2.28
.. slug: moving-linux-builds-to-glibc228
.. date: 2026-07-18 18:09:11 UTC
.. tags: 
.. category: 
.. link: 
.. description: 
.. type: text
.. author: mattip
-->

A short note for visibility.

PyPy builds tarballs of the compiler [ready for
download](https://downloads.python.org/pypy/). These include the latest
releases and also nightly builds, fresh from our fleet of buildbots. Over the
next couple of days, the nightly builds on linux will transition from
`manylinux2014` based docker images [to `manylinux2_28`
images](https://github.com/pypy/pypy-ci). The practical implication is that
nightly images, and the next releases, will require a minimum of `GLIBC>=2.28`,
i.e. AlmaLinux8, amanzonlinux 2023, debian 10, ubuntu 20.04. For a good
overview of how this glibc/distro/manylinux all works, see [the PEP 600 compliance
page](https://github.com/mayeut/pep600_compliance).

The next release will indicate this change by a new PyPy major version, 8.0.0.
It should include a Python3.12 interpreter, in which case it will be the last
release of the Python 3.11 interpreter.

