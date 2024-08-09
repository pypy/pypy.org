<!--
.. title: Conda-forge proposes sunsetting support for PyPy
.. slug: conda-forge-proposes-dropping-support-for-pypy
.. date: 2024-08-09 06:27:41 UTC
.. tags: conda-forge
.. category: 
.. link: 
.. description: 
.. type: text
.. author: mattip
-->

Conda-forge has kindly been providing support for PyPy since 2019. The
conda-forge team has been very patient and generous with resources, but it
seems the uptake of PyPy has not justified the effort. Major packages still
are not [available on PyPy](https://conda-forge.org/status/migration/?name=pypy38),
others find it hard to [update
versions](https://github.com/conda-forge/numpy-feedstock/pull/310). We don't
get much feedback at all about people using PyPy, and even less about PyPy on
conda-forge. The conda-forge team has proposed [sunsetting
PyPy](https://github.com/conda-forge/conda-forge.github.io/pull/2259) going
forward, which means current packages would remain but no new packages would be
built. If you have an opinion, you can comment on that PR, or on this blog post.

Since conda-forge supports PyPy3.9 but not PyPy3.10, we have continued
releasing PyPy3.9 even though we typically support only one version of PyPy3.
With the sunsetting proposal, we will not release any more updates to PyPy3.9.
I opened a [poll](https://github.com/orgs/pypy/discussions/4998) about the
intention to drop PyPy3.9. If you have an opinion, please chime in.
