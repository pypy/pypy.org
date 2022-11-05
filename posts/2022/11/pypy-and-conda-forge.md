<!--
.. title: PyPy and conda-forge
.. slug: pypy-and-conda-forge
.. date: 2022-11-05 17:00:25 UTC
.. tags: extension modules
.. category: 
.. link: 
.. description: 
.. type: text
.. author: mattip
-->

You can use PyPy as your python interpreter in a conda environment. The
conda-forge team has graciously provided this service.

The conda-forge [tips-and-tricks](
https://conda-forge.org/docs/user/tipsandtricks.html#using-pypy-as-an-interpreter)
page says:

> The conda-forge channel supports creating and installing packages into
> environments using the PyPy interpreter. Many packages are already available.
> You need to enable the conda-forge channel and use the pypy identifier when
> creating your environment:

```
  $ conda create -c conda-forge -n my-pypy-env pypy python=3.8
  $ conda activate my-pypy-env
```

> Currently supported python versions are 3.8 and 3.9. Support for pypy3.7 has
> been dropped. While you can still create a python 3.7 environment, you you
> will not be getting updates as new package versions are released (including
> pypy itself).

> if you are using defaults as a low priority channel, then you need to use
> strict channel priority as the metadata in defaults has not been patched yet
> which allows cpython extension packages to be installed alongside pypy.

```
  $ conda config --set channel_priority strict
```

The work required some out-of-the-box thinking on the part of conda-forge since
they needed to add the idea of a `pypy` identifier to the python version and
the whole conda team has been very supportive of the effort needed. Binary
packages are on offer for the usual platforms:

- `x86_64` windows, macos, linux
- `ppc64le` and `aarch64` linux.

There are [currently over 1000 packages](
https://conda-forge.org/status/#pypy38) available for download via the
conda-forge channel, and more are being added as the kind package maintainers
work around various differences between CPython and PyPy. Please let us know if
your favorite package is not supported.
