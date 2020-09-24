.. title: Download (advanced)
.. slug: download_advanced
.. date: 2019-12-28 16:14:02 UTC
.. tags: 
.. category: 
.. link: 
.. description: 

.. contents::
    :depth: 2

We provide pre-compiled binaries for many platforms and OSes:

* the Python2.7 compatible release — **PyPy2.7 v7.3.2**

* the Python3.6 compatible release — **PyPy3.6 v7.3.2**

* the Python2.7 Software Transactional Memory special release — **PyPy-STM 2.5.1** (Linux x86-64 only)

.. note::

  Our `nightly binary builds`_ have the most recent bugfixes and performance
  improvements, though they can be less stable than the official releases. See
  this link for `older versions`_.

.. _`nightly binary builds`: https://buildbot.pypy.org/nightly/
.. _`older versions`: https://downloads.python.org/pypy/

..
  table start

.. 
  Anonymous tags work, this kind of tag doesn't ``Download <linux64-pypy3.6>``

.. list-table:: `PyPy v7.3.2`_ 
   :widths: 20 20 20 40
   :header-rows: 1

   * - OS
     - PyPy3.6 
     - PyPy2.7
     - Notes

   * - **Linux x86 64 bit**
     - Download__
     - Download__
     - compatible with CentOS6 and later

   * - **Windows 32 bit**
     - Download__
     - Download__
     - compatible with any windows, 32- or 64-bit

       you might need the VC runtime library installer `vcredist.x86.exe`_

   * - **MacOS**

     - Download__
     - Download__
     - High Sierra >= 10.13, not for Sierra and below

   * - **Linux ARM64**

     - Download__
     - Download__
     - compatible with CentOS6 and later

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-linux64.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-linux64.tar.bz2

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-win32.zip
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-win32.zip

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-osx64.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-osx64.tar.bz2

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-aarch64.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-aarch64.tar.bz2

..
  table finish


.. list-table:: Other Platfoms
   :widths: 20 20 20 40
   :header-rows: 1

   * - OS
     - PyPy3.6
     - PyPy2.7
     - Notes

   * - **Linux x86 32 bit**

     - Download__
     - Download__
     - compatible with CentOS6 and later

   * - **PowerPC PPC64**

     - Download__
     - Download__
     - 64bit big-endian, Fedora 20 [1]_

   * - **PowerPC PPC64le**

     - Download__
     - Download__
     - 64bit little-endian, Fedora 21 [1]_

   * - **S390x**

     - Download__
     - Download__
     - built on Redhat Linux 7.2 [1]_

   



.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-linux32.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-linux32.tar.bz2

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-ppc64.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-ppc64.tar.bz2

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-ppc64le.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-ppc64le.tar.bz2

.. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-s390x.tar.bz2
.. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-s390x.tar.bz2

.. _`PyPy v7.3.2`: https://doc.pypy.org/en/latest/release-v7.3.2.html
.. _`vcredist.x86.exe`: https://www.microsoft.com/en-us/download/details.aspx?id=52685


.. _what's new in PyPy 7.3.2?: https://doc.pypy.org/en/latest/release-v7.3.2.html

.. [1]
  Linux binaries are provided for the
  distributions listed here.  **If your distribution is not exactly this
  one, it won't work,** you will probably see:
  ``pypy: error while loading shared libraries: ...``.

.. _`Default (with a JIT Compiler)`:

"JIT Compiler" version
-------------------------------

The binaries above include a Just-in-Time compiler. On x86-32, they only work on
CPUs that have the SSE2 instruction set (most of them do, nowadays).. They also
contain `stackless`_ extensions, like `greenlets`_.

Linux binaries and common distributions
---------------------------------------

Since version 7.3, the linux x86 binaries ship with versions
of OpenSSL, SQLite3, libffi, expat, and TCL/TK binary libraries linked in. This
make the binaries "portable" so that they should run on any current glibc-based
linux platform. The ideas were adopted from the `portable-pypy`_ package.

This solution to the portability problem means that the versions of the
packaged libraries are frozen to the version shipped, so updating your system
libraries will not affect this installation of PyPy. Also see the note about
SSL certificates below.

For aarch64, s390x, and ppc64, the binaries target a specific operating system.
These binaries are dynamically linked, and thus might not be usable due to the
sad story of linux binary compatibility.  This means that **Linux binaries are
only usable on the distributions written next to them** unless you're ready to
hack your system by adding symlinks to the libraries it tries to open.  There
are better solutions:

* download PyPy from your release vendor (usually an outdated
  version): `Ubuntu`_ (`PPA`_), `Debian`_, `Homebrew`_, MacPorts,
  `Fedora`_, `Gentoo`_ and `Arch`_ are known to package PyPy, with various
  degrees of being up-to-date. FreshPorts_ packages for FreeBSD.

* use conda_, which will also enable installing binary-compiled packages.

* `recompile the CFFI-based`_ TCL/TK, OpenSSL, or sqlite3 modules, using system
  libraries and the scripts in ``pypy/lib_pypy``. This solution will not solve
  compatibility issues with libffi, since that is baked into PyPy.

* or translate_ your own PyPy.

.. note::

    SSL Certificates

    While the linux binaries ship an OpenSSL library, they do not ship a
    certificate store for SSL certificates. If you wish to use SSL module,
    you will need a valid certificate store. You can use the `certifi`_ package
    and set ``SSL_CERT_FILE`` to ``certifi.where()`` or install your platform
    certificates which should be discovered by the ``_ssl`` module.


.. _`Ubuntu`: https://packages.ubuntu.com/search?keywords=pypy&searchon=names
.. _`PPA`: https://launchpad.net/~pypy/+archive/ppa
.. _`Debian`: https://packages.debian.org/sid/pypy
.. _`Fedora`: https://fedoraproject.org/wiki/Features/PyPyStack
.. _`Gentoo`: https://packages.gentoo.org/package/dev-python/pypy
.. _`Homebrew`: https://github.com/Homebrew/homebrew-core/blob/master/Formula/pypy.rb
.. _`Arch`: https://wiki.archlinux.org/index.php/PyPy
.. _`portable-pypy`: https://github.com/squeaky-pl/portable-pypy#portable-pypy-distribution-for-linux
.. _`recompile the CFFI-based`: https://doc.pypy.org/en/latest/build.html#build-cffi-import-libraries-for-the-stdlib
.. _`certifi`: https://pypi.org/project/certifi/
.. _conda: https://conda-forge.org/blog/posts/2020-03-10-pypy/


Previous version can be downloaded from here__, or directly from the buildbot's
mirror_.

.. __: https://downloads.python.org/pypy/
.. _mirror: https://buildbot.pypy.org/mirror/
.. _FreshPorts: https://www.freshports.org/lang/pypy


If your CPU is really, really old, it may be a x86-32 without SSE2.
There is untested support for manually translating PyPy's JIT without
SSE2 (``--jit-backend=x86-without-sse2``) but note that your machine
is probably low-spec enough that running CPython on it is a better
idea in the first place.

PyPy-STM 2.5.1
------------------------------

This is a special version of PyPy!  See the `Software Transactional
Memory`_ (STM) documentation.

* `PyPy-STM Linux x86-64 binary (64bit, tar.bz2 built on Ubuntu 12.04 - 16.04)`__

.. _`Software Transactional Memory`: https://doc.pypy.org/en/latest/stm.html
.. __: https://downloads.python.org/pypy/pypy-stm-2.5.1-linux64.tar.bz2


.. _`Other versions (without a JIT)`:

Other versions
-------------------------------

The other versions of PyPy are:

* Try the most up-to-date `nightly binary builds`_ , if the official
  release is too old for what you want to do.

* Reverse debugger: This version enables debugging your Python
  programs by going forward and backward in time.  See the `RevDB
  documentation`__.

.. __: https://foss.heptapod.net/pypy/revdb/

* Old-style sandboxing: A special safe version.
  *This is NOT the version announced in-development during 2019!*
  Read the docs about sandboxing_.
  This version is **not supported** and not actively maintained.  You
  will likely have to fix some issues yourself, or checkout an old
  version, or otherwise play around on your own.  We provide this
  documentation only for historical reasons.  Please do not use in
  production.  For reference, there are some very old, unmaintained
  binaries for Linux (32bit__, 64bit__).

.. __: https://downloads.python.org/pypy/pypy-1.8-sandbox-linux64.tar.bz2
.. __: https://downloads.python.org/pypy/pypy-1.8-sandbox-linux.tar.bz2
.. _`sandbox docs`: https://doc.pypy.org/en/latest/sandbox.html

.. _`nightly binary builds`: https://buildbot.pypy.org/nightly/

Installing
----------

All binary versions are packaged in a ``tar.bz2`` or ``zip`` file.  When
uncompressed, they run in-place.  You can uncompress them
either somewhere in your home directory or, say, in ``/opt``.
If you want, put a symlink from somewhere like
``/usr/local/bin/pypy`` to ``/path/to/pypy_expanded/bin/pypy``.  Do
not move or copy the executable ``pypy`` outside the tree --- put
a symlink to it, otherwise it will not find its libraries.


Installing more modules
-------------------------------

There are as yet few distribution-ready packages. `conda`_ is one easy
way to get packages with a minimum of compilation.
We recommend installing ``pip``, which is the standard package
manager of Python.  It works like it does on CPython as explained in the
`installation documentation`_. 

If you use your distribution's PyPy package we recommend you install packages
into a virtualenv. If you try to build a module and the build process complains
about "missing Python.h", you may need to install the pypy-dev package.

.. _installation documentation: https://doc.pypy.org/en/latest/install.html

.. _translate:

Building from source
--------------------

(see more build instructions_)


1. Get the source code.  The preferred way is to checkout the current
   trunk using Mercurial_.  The trunk usually works and is of course
   more up-to-date:

   .. code-block:: bash

     hg clone https://foss.heptapod.net/pypy/pypy

   The trunk contains PyPy 2.  For PyPy 3, switch to the correct branch:

   .. code-block:: bash

     # switch to the branch that implements Python 3.6
     hg update py3.6

   Alternatively, get one of the following smaller packages for the source at
   the same revision as the above binaries:

   * `pypy2.7-v7.3.2-src.tar.bz2`__ (sources, PyPy 2 only)
   * `pypy3.6-v7.3.2-src.tar.bz2`__ (sources, PyPy 3 only)

   .. __: https://downloads.python.org/pypy/pypy2.7-v7.3.2-src.tar.bz2
   .. __: https://downloads.python.org/pypy/pypy3.6-v7.3.2-src.tar.bz2


2. Make sure you **installed the dependencies.**  See the list here__.

   .. __: https://pypy.readthedocs.org/en/latest/build.html#install-build-time-dependencies

3. Enter the ``goal`` directory:

   .. code-block:: bash

     cd pypy/pypy/goal

4. Run the ``rpython`` script.  Here are the common combinations
   of options (works also with ``python`` instead of ``pypy``;
   requires CPython 2.7 or PyPy 2, even to build PyPy 3):

   .. code-block:: bash

     # get the JIT version
     pypy ../../rpython/bin/rpython -Ojit targetpypystandalone
     # get the no-jit version
     pypy ../../rpython/bin/rpython -O2 targetpypystandalone
     # get the sandbox version
     pypy ../../rpython/bin/rpython -O2 --sandbox targetpypystandalone

5. Enjoy Mandelbrot ``:-)``  It takes on the order of half an hour to
   finish the translation, and about 3GB of RAM on a 32-bit system
   and about 5GB on 64-bit systems.  (Do not start a translation on a
   machine with insufficient RAM!  It will just swap forever.  See
   notes below in that case.)

6. If you want to install this PyPy as root, please read the next section,
   Packaging_.

Notes:

* It is recommended to use PyPy to do translations, instead of using CPython,
  because it is twice as fast.  You should just start by downloading an
  official release of PyPy (with the JIT).  If you really have to use CPython
  then note that we are talking about CPython 2.7 here, not CPython 3.x.
  (Older versions like 2.6 are out.)

* On some 32-bit systems, the address space limit of 2 or 3 GB of RAM
  can be an issue.  More generally you may be just a little bit low of
  RAM.  First note that 2 GB is really not enough nowadays; on Windows
  you first need to refer to the `Windows build instructions`_.  More
  precisely, translation on 32-bit takes at this point 2.7 GB if PyPy is
  used and 2.9 GB if CPython is used.  There are two workarounds:

  1. use PyPy, not CPython.  If you don't have any PyPy so far, not even
  an older version, then you need to build one first, with some parts
  removed.  So, first translate with:

  .. code-block:: shell

     cpython2 rpython -Ojit targetpypystandalone \
     --withoutmod-micronumpy --withoutmod-cpyext

  then copy ``pypy-c`` and ``libpypy_c.so`` somewhere else, and finally
  call it with ``...pypy-c ../../rpython/bin/rpython -Ojit``.

  2. if even using PyPy instead of CPython is not enough, try to tweak
  some internal parameters.  Example (slower but saves around 400MB):

  .. code-block:: bash

    PYPY_DONT_RUN_SUBPROCESS=1 PYPY_GC_MAX_DELTA=200MB \
    pypy --jit loop_longevity=300 ../../rpython/bin/rpython \
    -Ojit --source
    # then read the next point about --source

* You can run translations with ``--source``, which only builds the C
  source files (and prints at the end where).  Then you can ``cd`` there
  and execute ``make``.  This is another way to reduce memory usage.
  Note that afterwards, you have to run manually ``pypy-c
  .../pypy/tool/build_cffi_imports.py`` if you want to be able to import
  the cffi-based modules.

* Like other JITs, PyPy doesn't work out of the box on some Linux
  distributions that trade full POSIX compliance for extra security
  features.  E.g. with PAX, you have to run PyPy with ``paxctl -cm``.
  This also applies to translation (unless you use CPython to run the
  translation and you specify ``--source``).

.. _instructions: https://pypy.readthedocs.org/en/latest/build.html
.. _`x86 (IA-32)`: https://en.wikipedia.org/wiki/IA-32
.. _`x86-64`: https://en.wikipedia.org/wiki/X86-64
.. _SSE2: https://en.wikipedia.org/wiki/SSE2
.. _`contact us`: contact.html
.. _`sandboxing`: features.html#sandboxing
.. _`stackless`: https://www.stackless.com/
.. _`greenlets`: https://pypy.readthedocs.org/en/latest/stackless.html#greenlets
.. _`Windows build instructions`: https://doc.pypy.org/en/latest/windows.html#preparing-windows-for-the-large-build
.. _`shadow stack`: https://pypy.readthedocs.org/en/latest/config/translation.gcrootfinder.html
.. _Mercurial: https://www.mercurial-scm.org/

Packaging
---------

Once PyPy is translated from source, a binary package similar to those
provided in the section `Default (with a JIT Compiler)`_ above can be
created with the ``package.py`` script:

.. code-block:: bash

    cd ./pypy/pypy/tool/release/
    python package.py --help  # for information
    python package.py --archive-name pypy-my-own-package-name

It is recommended to use package.py because custom scripts will
invariably become out-of-date.  If you want to write custom scripts
anyway, note an easy-to-miss point: some modules are written with CFFI,
and require some compilation.  If you install PyPy as root without
pre-compiling them, normal users will get errors:

* PyPy 2.5.1 or earlier: normal users would see permission errors.
  Installers need to run ``pypy -c "import gdbm"`` and other similar
  commands at install time; the exact list is in `package.py`_.  Users
  seeing a broken installation of PyPy can fix it after-the-fact if they
  have sudo rights, by running once e.g. ``sudo pypy -c "import gdbm``.

* PyPy 2.6 and later: anyone would get ``ImportError: no module named
  _gdbm_cffi``.  Installers need to run ``pypy _gdbm_build.py`` in the
  ``lib_pypy`` directory during the installation process (plus others;
  see the exact list in `package.py`_).  Users seeing a broken
  installation of PyPy can fix it after-the-fact, by running ``pypy
  /path/to/lib_pypy/_gdbm_build.py``.  This command produces a file
  called ``_gdbm_cffi.pypy-41.so`` locally, which is a C extension
  module for PyPy.  You can move it at any place where modules are
  normally found: e.g. in your project's main directory, or in a
  directory that you add to the env var ``PYTHONPATH``.

.. _`package.py`: https://bitbucket.org/pypy/pypy/src/default/pypy/tool/release/package.py


.. 
  checksum start

Checksums
---------

Here are the checksums for latest downloads

pypy3.6-7.3.2 sha256::

    64d6a0503c83dd328e1a6bf7fcb2b2e977c1d27c6fcc491a7174fd37bc32a12  pypy3.6-v7.3.2-aarch64.tar.bz2
    6fa871dedf5e60372231362d2ccb0f28f623d42267cabb49be11a3e10bee2726  pypy3.6-v7.3.2-linux32.tar.bz2
    d7a91f179076aaa28115ffc0a81e46c6a787785b2bc995c926fe3b02f0e9ad83  pypy3.6-v7.3.2-linux64.tar.bz2
    fd457bfeaf54aa69417b6aa4817df40e702dc8aaaf7e83ba005d391a1bddfa96  pypy3.6-v7.3.2-osx64.tar.bz2
    16afbaa245c016c054d9300c19433efcc76c50664ff2c86d913ff76ed0a729dc  pypy3.6-v7.3.2-s390x.tar.bz2
    fd6175fed63ff9fccd7886068078853078948d98afae9bd4f5554c6f7873c10d  pypy3.6-v7.3.2-src.tar.bz2
    edcbcd3598a91de3115f86550d1bc76ac46fc0a3e86a1e951769a993f6fbcbf0  pypy3.6-v7.3.2-src.zip
    13a39d46340afed20f11de24e9068968386e4bb7c8bd168662711916e2bf1da6  pypy3.6-v7.3.2-win32.zip

pypy3.7-7.3.2 sha256::

    c5c35a37917f759c19e2a6b3df3b4d56298faa2fae83c143469bcbda42ca5dd2  pypy3.7-v7.3.2-aarch64.tar.bz2
    34c7e1c7bd06e437ad43cc90a20f9444be1f0a264d0955e32098294c30274784  pypy3.7-v7.3.2-linux32.tar.bz2
    a285ddcbc909d68c648585fae4f33b0ba24961bb4e8fafe5874cf725d6e83df6  pypy3.7-v7.3.2-linux64.tar.bz2
    337dd4d9e529d2f221e0beb092236c18430e0564ab835c6bba425a1daf7c9958  pypy3.7-v7.3.2-osx64.tar.bz2
    d4ce71ebba148bf83c24fc963e8282c9b7f0c81fcf6b612301b8efe6bd7658d1  pypy3.7-v7.3.2-s390x.tar.bz2
    9274186eb0c28716a8c6134803b1df857bc3f496e25e50e605c4d95201c8817d  pypy3.7-v7.3.2-src.tar.bz2
    23363123c607058dac29995cf281c4609a8d8d278841a8f05ea8559bdb1678a8  pypy3.7-v7.3.2-src.zip
    e3c589be07760bc3042981c379b7fd1603e832a4db426075f09e090473846a96  pypy3.7-v7.3.2-win32.zip

pypy2.7-7.3.2 sha256::

    fce1f06f20ab8bcacb9ac1c33572d6425033de53c3a93fbd5391189cc3e106cb  pypy2.7-v7.3.2-aarch64.tar.bz2
    78f30ac17abe3cc077fc2456ef55adb51b052c5126011b2a32bacc858acaca7d  pypy2.7-v7.3.2-linux32.tar.bz2
    8d4f08116a97153a0f739de8981874d544b564cbc87dd064cca33f36c29da13b  pypy2.7-v7.3.2-linux64.tar.bz2
    10ca57050793923aea3808b9c8669cf53b7342c90c091244e9660bf797d397c7  pypy2.7-v7.3.2-osx64.tar.bz2
    042d5e99f660de098de979c4b27f7f8c1332d904db379bb2bf2c3402729749bb  pypy2.7-v7.3.2-s390x.tar.bz2
    8189480d8350ad6364d05c2b39fd7d832644d4b1cd018f785126389df45928d1  pypy2.7-v7.3.2-src.tar.bz2
    d891c55f4e657b5e3fe609cee02b2288790abb5554a544ca047f088310d129c4  pypy2.7-v7.3.2-src.zip
    0fd62265e0421a02432f10a294a712a5e784a8e061375e6d8ea5fd619be1be62  pypy2.7-v7.3.2-win32.zip

pypy2.7-7.3.1 sha256::

    094f23ab262e666d8740bf27459a6b1215a628dad9b6c2a88f1ed5c793fab267  pypy2.7-v7.3.1-aarch64.tar.bz2
    cd155d06cd0956d9de4a16e8a6bdf0722cb45b5bc4bbf805825d393ebd6690ad  pypy2.7-v7.3.1-linux32.tar.bz2
    be74886547df7bf7094096a11fc0a48496779d0d1b71901797b0c816f92caca3  pypy2.7-v7.3.1-linux64.tar.bz2
    dfd4651243441d2f8f1c348e9ecc09848642d0c31bb323aa8ac320e5b9f232f0  pypy2.7-v7.3.1-osx64.tar.bz2
    1b65e085118e44ac57d38a9ba79516c68bf1fdcd65c81c66b5b5ffff06b4463b  pypy2.7-v7.3.1-ppc64.tar.bz2
    d81c7177e25bd8b1c99081e32362a29ee467ccd310b17a11161f4a9b96222b20  pypy2.7-v7.3.1-ppc64le.tar.bz2
    71ad5132a6fd32af0b538c17ebd1e0bfe5f5dfa74b129bce242bd28357bf35fc  pypy2.7-v7.3.1-s390x.tar.bz2
    fa3771514c8a354969be9bd3b26d65a489c30e28f91d350e4ad2f4081a9c9321  pypy2.7-v7.3.1-src.tar.bz2
    71d764c94f467f9dd75b6af086e2b69e0d520bf6227bcb39055c24c799c135be  pypy2.7-v7.3.1-src.zip
    e3c0dfb385d9825dd7723f26576d55d43ed92f1178f2399ab39e9fa11621a47b  pypy2.7-v7.3.1-win32.zip

pypy3.6-7.3.1 sha256::

    0069bc3c1570b935f1687f5e128cf050cd7229309e48fad2a2bf2140d43ffcee  pypy3.6-v7.3.1-aarch64.tar.bz2
    2e7a818c67f3ac0708e4d8cdf1961f30cf9586b3f3ca2f215d93437c5ea4567b  pypy3.6-v7.3.1-linux32.tar.bz2
    f67cf1664a336a3e939b58b3cabfe47d893356bdc01f2e17bc912aaa6605db12  pypy3.6-v7.3.1-linux64.tar.bz2
    d9c1778cd1ba37e129b495ea0f35ccdd9b68f5cd9d33ef0ce24e955c16d8840b  pypy3.6-v7.3.1-osx64.tar.bz2
    ee02b3e65f0ca49dc09850b57835c2b65d1234f26f7991027ca6d65fadbaa4d9  pypy3.6-v7.3.1-ppc64.tar.bz2
    089fd806629ebf79cb0cb4b0c303d8665f360903b79f0df9214b58dbc42e8231  pypy3.6-v7.3.1-ppc64le.tar.bz2
    147592888e25678c1ae1c2929dc7420b3a0990117fdb25f235cb22476b4e4b5a  pypy3.6-v7.3.1-s390x.tar.bz2
    0c2cc3229da36c6984baee128c8ff8bb4516d69df1d73275dc4622bf249afa83  pypy3.6-v7.3.1-src.tar.bz2
    91e7ba30519f2c4c1833280acfb660b48392ef57c5ed0fa4e8af78587a7b8f20  pypy3.6-v7.3.1-src.zip
    752fbe8c4abee6468e5ce22af82818f821daded36faa65f3d69423f9c217007a  pypy3.6-v7.3.1-win32.zip

pypy2.7-7.3.0 sha256::

    a3dd8d5e2a656849fa344dce4679d854a19bc4a096a0cf62b46a1be127a5d56c  pypy2.7-v7.3.0-aarch64.tar.bz2
    eac1308b7d523003a5f6d20f58406d52ab14611bcec750122ae513a5a35110db  pypy2.7-v7.3.0-linux32.tar.bz2
    f4950a54378ac637da2a6defa52d6ffed96af12fcd5d74e1182fb834883c9826  pypy2.7-v7.3.0-linux64.tar.bz2
    ca7b056b243a6221ad04fa7fc8696e36a2fb858396999dcaa31dbbae53c54474  pypy2.7-v7.3.0-osx64.tar.bz2
    82e62869812aa2953a4f83e96c813cbc52973dfa5e42605e72b6610ac13f2481  pypy2.7-v7.3.0-ppc64.tar.bz2
    592a6db77270b922ffa13cbeced9eabbc36c532ded9fc145f6a19073d3e78499  pypy2.7-v7.3.0-ppc64le.tar.bz2
    d254b82a00021339762198e41ba7f72316010d0f9bd4dcd7b0755185da9c005e  pypy2.7-v7.3.0-s390x.tar.bz2
    b0b25c7f8938ab0fedd8dedf26b9e73c490913b002b484c1b2f19d5844a518de  pypy2.7-v7.3.0-src.tar.bz2
    42dc84a277e7a5e635fe39bbd745f06135902c229a257123332b7555800d915b  pypy2.7-v7.3.0-src.zip
    a9e3c5c983edba0313a41d3c1ab55b080816c4129e67a6c272c53b9dbcdd97ec  pypy2.7-v7.3.0-win32.zip

pypy3.6-7.3.0 sha256::

    b900241bca7152254c107a632767f49edede99ca6360b9a064141267b47ef598  pypy3.6-v7.3.0-aarch64.tar.bz2
    7045b295d38ba0b5ee65bd3f078ca249fcf1de73fedeaab2d6ad78de2eab0f0e  pypy3.6-v7.3.0-linux32.tar.bz2
    d3d549e8f43de820ac3385b698b83fa59b4d7dd6cf3fe34c115f731e26ad8856  pypy3.6-v7.3.0-linux64.tar.bz2
    87b2545dad75fe3027b4b2108aceb9fdadcdd24e61ae312ac48b449fdd452bf3  pypy3.6-v7.3.0-osx64.tar.bz2
    e2587e8da2abb12a86bf75941ce739124d2a1156367a9a3d729ac31d0841c300  pypy3.6-v7.3.0-ppc64.tar.bz2
    d6f3b701313df69483b43ebdd21b9652ae5e808b2eea5fbffe3b74b82d2e7433  pypy3.6-v7.3.0-ppc64le.tar.bz2
    0fe2f7bbf42ea88b40954d7de773a43179a44f40656f2f58201524be70699544  pypy3.6-v7.3.0-s390x.tar.bz2
    48d12c15fbcbcf4a32882a883195e1f922997cde78e7a16d4342b9b521eefcfa  pypy3.6-v7.3.0-src.tar.bz2
    8ae9efd0a2aadb19e892bbd07eca8ef51536296a3ef93964149aceba511e79ca  pypy3.6-v7.3.0-src.zip
    30e6870c4f3d8ef91890a6556a98080758000ba7c207cccdd86a8f5d358998c1  pypy3.6-v7.3.0-win32.zip

pypy2.7-7.2.0 sha256::

    57b0be053c6a5f069e23b843f38863cf7920f5eef7bc89f2e086e5c3a28a2ba9  pypy2.7-v7.2.0-aarch64.tar.bz2
    76d666e5aee54b519d6ec1af4ef0cbdc85f7f9276dd554e97deb026adfd0c936  pypy2.7-v7.2.0-linux32.tar.bz2
    05acf28e6a243026ecad933b9361d8f74b41f00818071b76b38c4694cc4c9599  pypy2.7-v7.2.0-linux64.tar.bz2
    36aa2f2440e762333569118dd0b3d5371d575c40966effa194d116c5453ddb52  pypy2.7-v7.2.0-osx64.tar.bz2
    fb51150a4ce94b0ca8587899ba69c41fc58a6b35c5340ea6926376ecb9cfcac4  pypy2.7-v7.2.0-ppc64.tar.bz2
    5c4224525657c29b815cb2c6b3f9bc5a267368cc6adf0fedb235a6052929f65f  pypy2.7-v7.2.0-ppc64le.tar.bz2
    bb7ae585ecb4d904c890e28a2c5b6bd379f57cc3d9e38ff45597ff54fa935eaa  pypy2.7-v7.2.0-s390x.tar.bz2
    55cb7757784fbe3952102447f65b27d80e6c885a464a7af1a9ce264492439dcc  pypy2.7-v7.2.0-src.tar.bz2
    897038550614d558f9f6718409b107e27903ef2b2b57ec250939d1b1ebdf0aba  pypy2.7-v7.2.0-src.zip
    956eeaaaac053e5d0917e77a3d2ad1933ab5561eb3e6e71235780b5aa5fd2bb7  pypy2.7-v7.2.0-win32.zip

pypy2.7-7.1.1 sha256::

    41ca390a76ca0d47b8353a0d6a20d5aab5fad8b0bb647b960d8c33e873d18ef5  pypy2.7-v7.1.1-linux32.tar.bz2
    73b09ef0860eb9ad7997af3030b22909806a273d90786d78420926df53279d66  pypy2.7-v7.1.1-linux64.tar.bz2
    31a17294dec96c2191885c776b4ee02112957dc874f7ba03e570537a77b78c35  pypy2.7-v7.1.1-osx64.tar.bz2
    1ef94c3a9c67c2335cee0b21753036b4696ed588b9d54b7b8036a6ae47f7001d  pypy2.7-v7.1.1-s390x.tar.bz2
    5f06bede6d71dce8dfbfe797aab26c8e35cb990e16b826914652dc093ad74451  pypy2.7-v7.1.1-src.tar.bz2
    d9b07a2954ad6dbde94feffd848311e2b5169563d33e3e9f17969579b01a4158  pypy2.7-v7.1.1-src.zip
    9c59226311f216a181e70ee7b5aa4d9665a15d00f24ae02acec9af7d96355f63  pypy2.7-v7.1.1-win32.zip

pypy2.7-7.1.0 sha256::

    44ec91e8cb01caab289d8763c203f3aaf288d14325a6c42692bd1ac4e870d758  pypy2.7-v7.1.0-linux32.tar.bz2
    fef176a29a2ef068c00c8098e59dab935ca6e956f089672b3f7351da95a034f5  pypy2.7-v7.1.0-linux64.tar.bz2
    8be43685ce718b0768387450fc6dc395d60809b778b6146c353ef67826022153  pypy2.7-v7.1.0-osx64.tar.bz2
    b065f55741bcb37863f1eca30ce91c9d79159371a6994100930cdc2ede3237bc  pypy2.7-v7.1.0-s390x.tar.bz2
    b051a71ea5b4fa27d0a744b28e6054661adfce8904dcc82500716b5edff5ce4b  pypy2.7-v7.1.0-src.tar.bz2
    e60ce30f9947844da43daaa7658adc0c05330681305225954114772f42df06ec  pypy2.7-v7.1.0-src.zip
    76658c9ad679d562b8b6a09d006caa666406337b9834ff56db16980c5e549f20  pypy2.7-v7.1.0-win32.zip

pypy3.6-7.2.0 sha256::

    f82dc9dc6c692417ee9727f23beae75364a5757ebdc657a2a1d0010ac3ad17ab  pypy3.6-v7.2.0-aarch64.tar.bz2
    45e99de197cb3e974cfc8d45e0076ad2066852e61e56b3eafd1237efafd2c43e  pypy3.6-v7.2.0-linux32.tar.bz2
    aa128e555ad0fe5c4c15104ae0903052bd232b6e3a73f5fe023d27b8fd0d6089  pypy3.6-v7.2.0-linux64.tar.bz2
    836abb0ec303b90a684533711ed3b8269d3e8c64805b595e410920abdea678ac  pypy3.6-v7.2.0-osx64.tar.bz2
    14021d196e393b3a6d2395ab94ceec347753715e37223efe4c50b7c141b351a2  pypy3.6-v7.2.0-ppc64.tar.bz2
    6aef73a3b68e9a6c062cadd83d3db16790960cf97401ca6f2aad2195e9b05c35  pypy3.6-v7.2.0-ppc64le.tar.bz2
    a11da8118064db102d159e9221319c428b298c4a87f26166fd6ae94be8d6ae0d  pypy3.6-v7.2.0-s390x.tar.bz2
    0d7c707df5041f1593fe82f29c40056c21e4d6cb66554bbd66769bd80bcbfafc  pypy3.6-v7.2.0-src.tar.bz2
    405ac35695dd374d5ea192cb44cb47231f9a65812cc7b6549df33df12ffe54db  pypy3.6-v7.2.0-src.zip
    c926f622bec24a8b348591d631717ace83b3a6c3c2dac02b157b622b97d1fc9c  pypy3.6-v7.2.0-win32.zip

pypy3.6-7.1.1 sha256::

    cb11ef4b0df569c28390b1ee93029159e1b90bfbad98df6abd629d5203b2abd9  pypy3.6-v7.1.1-linux32.tar.bz2
    8014f63b1a34b155548852c7bf73aab2d41ebddf2c8fb603dc9dd8509be93db0  pypy3.6-v7.1.1-linux64.tar.bz2
    a5c2f2bfa2b4a4d29e8a67baab95699b169054066df218a14f171bb84a6df0c0  pypy3.6-v7.1.1-osx64.tar.bz2
    4a91bf2d9a142b6dbf82b5301cb510535ae9a54e1645546b2e0735a7b5ed85ba  pypy3.6-v7.1.1-s390x.tar.bz2
    6a3ef876e3691a54f4cff045028ec3be94ab9beb2e99f051b83175302c1899a8  pypy3.6-v7.1.1-src.tar.bz2
    4a3ebeb767740f2dc0b886d02797d21d7d69f154cf951bb991c19bd485e6cae1  pypy3.6-v7.1.1-src.zip
    8b513b254de5f31890f5956569de9aec3a0a91d7aba72fc89d66901f4a8ccf49  pypy3.6-v7.1.1-win32.zip

pypy 3.6-v7.1.0 sha256::


    031bfac61210a6e161bace0691b854dc15d01b0e624dc0588c544ee5e1621a83  pypy3.6-v7.1.0-linux32.tar.bz2
    270dd06633cf03337e6f815d7235e790e90dabba6f4b6345c9745121006925fc  pypy3.6-v7.1.0-linux64.tar.bz2
    d46e005ba095cb4a7006079ffbf4fe63c18cf5e9d8ce9ce8383efc1a4863ab5b  pypy3.6-v7.1.0-osx64.tar.bz2
    243cd0cc188a94c1f064f402ae72b8ba4303eb3137eac53c53826472b8005098  pypy3.6-v7.1.0-s390x.tar.bz2
    faa81f469bb2a7cbd22c64f22d4b4ddc5a1f7c798d43b7919b629b932f9b1c6f  pypy3.6-v7.1.0-src.tar.bz2
    4858e7e8a0007bc3b381bd392208b28d30889a4e5a88a3c28e3d9dc4f25b654e  pypy3.6-v7.1.0-src.zip
    77a0576a3d518210467f0df2d0d9a1892c664566dc02f25d974c2dbc6b4749e7  pypy3.6-v7.1.0-win32.zip

