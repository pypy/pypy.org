.. title: Repeated string concatenation is quadratic in PyPy (and CPython)
.. slug: string-concatenation-quadratic
.. date: 2023-01-05 18:00:00 UTC
.. tags: performance
.. category:
.. link:
.. description:
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

This is a super brief blog post responding to an issue_ that we got on the PyPy
issue tracker. I am moving my response to the blog (with permission of the
submitter) to have a post to point to, since it's a problem that comes up with
some regularity.

The issue pointed out that a small program that operates on strings is much
slower on PyPy compared to CPython. The program is a solution for this year's
Advent of Code `Day 16`_ and looks like this:

.. code:: python

    def dragon(a):
        b = a[::-1].replace('0','r').replace('1','0').replace('r','1')
        return a+'0'+b

    def diffstr(a):
        b = ""
        for i in range(0,len(a),2):
            b += ['0','1'][a[i] == a[i+1]]
        return b

    def iterdiff(a):
        b = a
        while(len(b) % 2 == 0):
            b = diffstr(b)
        return b

    size = 35651584
    initstate = '10010000000110000'
    while(len(initstate) < size):
        initstate = dragon(initstate)
    initstate = initstate[:size]
    print(iterdiff(initstate))

The submitter pointed out, that the program is fast on CPython (~8s on my
laptop) and slow (didn't finish) on PyPy.

The reason for the performance difference is that ``+=`` on strings in a loop
has quadratic complexity in PyPy, which is what ``diffstr`` does. To see the
quadraticness, consider that to add a character at the end of the string, the
beginning of the string needs to be copied into a new chunk of memory. If the
loop runs ``n`` times, that means there are ``1 + 2 + 3 + ... + n = n * (n + 1)
// 2`` character copies.

Repeated string concatenations are in principle also quadratic in CPython, but
CPython has an optimization_ that makes them sometimes not quadratic, which is
what makes this program not too slow in CPython.

.. _optimization: https://docs.python.org/2/whatsnew/2.4.html#optimizations

In order to fix the problem on PyPy it's best to use a list for the string
parts, which as the right amortized O(1) complexity for ``.append`` calls, and
then use ``str.join`` after the loop:

.. code:: python

    def diffstr(a):
        b = []
        for i in range(0,len(a),2):
            b.append(['0','1'][a[i] == a[i+1]])
        return "".join(b)

With this change the program becomes a little bit faster on CPython for me, and
on PyPy it stops being quadratic and runs in ~3.5s.

In general, it's best not to rely on the presence of this optimization in
CPython either. Sometimes, a small innocent looking changes will break CPython's
optimization. E.g. this useless change makes CPython also take ages:


.. code:: python

    def diffstr(a):
        b = ""
        for i in range(0,len(a),2):
            b += ['0','1'][a[i] == a[i+1]]
            c = b
        return b

The reason why this change breaks the optimization in CPython is that it only
triggers if the reference count of ``b`` is 1, in which case it uses ``realloc``
on the string. The change is unrealistic of course, but you could imagine a
related that keeps an extra reference to ``b`` for a sensible reason.

Another situation in which the optimization doesn't work is discussed in this
`StackOverflow question`_ with an answer by Tim Peters.

.. _`StackOverflow question`: https://stackoverflow.com/a/44487738 

It's unlikely that PyPy will fix this. We had a prototype how to do it, but it
seems very little "production" code uses `+=` on strings in a loop, and the fix
makes the strings implementation quite a bit more complex.

So, in summary, don't use repeated concatenations in a loop!

.. _issue: https://foss.heptapod.net/pypy/pypy/-/issues/3885
.. _`Day 16`: https://adventofcode.com/2016/day/16
