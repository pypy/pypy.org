<!--
.. title: Better JIT Support for Auto-Generated Python Code
.. slug: jit-auto-generated-code
.. date:
.. tags: 
.. category: 
.. link: 
.. description: 
.. type: text
.. author: cfbolz
-->

# Performance Cliffs

A common bad property of many different JIT compilers is that of a "performance
cliff": A seemingly reasonable code change, leading to massively reduced
performance due to hitting some weird property of the JIT compiler that's not
easy to understand for the programmer. Hitting a performance cliff as a
programmer can be intensely frustrating and turn people off from using PyPy
altogether. Recently we've been working on trying to remove some of PyPy's
performance cliffs, and this post describes one such effort.

The problem showed up in an issue where somebody described found the performance
of their website using Tornado a lot worse than what various benchmarks
suggested. It took some careful digging down into the problem to figure out what
caused the problem, this blog post will be about how we solved it.

# Trace Limits and Inlining

To understand why the problem occurs, it's necessary to understand how PyPy's
trace limit and inlining works. The tracing JIT has a maximum trace length built
in, the reason for that is some limitation in the compact encoding of traces in
the JIT. Another reason is that we don't want to generate arbitrary large chunks
of machine code. Usually, when we hit the trace limit, it is due to *inlining*.
While tracing, the JIT will inline many of the functions called from the
outermost one. This can lead to the trace being too long. If that happens, we
will mark a called function as uninlinable and the next time we trace the outer
function we won't inline it, leading to a shorter trace, which hopefully fits
the trace limit.

IMAGE

This is where the problem occurs: sometimes, the outermost function itself
doesn't fit the trace limit, without any inlining going on at all. This is
usually not the case for normal, hand-written Python functions. However, it can
happen for automatically generated Python code, such as the code that the
Tornado templating engine produces.

This is what used to happen in such a situation: the function is traced until
the trace is too long. Then the trace limits stops further tracing. This happens
again and again. The effect is that the function is even slowed down: we spend
time tracing it, but that effort is never useful, so the resulting execution is
slower than not using the JIT at all!


# Solution

To get out of the endless cycle of useless retracing we first had the idea of
simply disable all code generation for such functions, that produce too long
traces even if there is no inlining at all. However, that lead to disappointing
performance, because important parts of the code were always interpreted.

Instead, our solution is now as follows: After we have hit the trace limit and
no inlining has happened so far, we mark that function as a source of huge
traces. The next time we trace such a function, we do so in a special mode. In
that mode, hitting the trace limit behaves differently: Instead of stopping the
tracer and throwing away the trace produced so far, we will use the unfinished
trace to produce machine code. The question is what should happen when execution
reaches the end of the unfinished trace. We want to be able to extend the trace
from that point and add another piece of machine code, but not do that too
eagerly to prevent lots and lots of machine code being generated. To achieve
this behaviour we add a guard to the end of the unfinished trace, which will
always fail. This has the right behaviour: a failing guard will transfer control
to the interpreter, but if it fails often enough, we can patch it to jump to
more machine code, that starts from this position. In that way, we can slowly
explore the full gigantic function and add all those parts of the control flow
graph that are actually commonly executed at runtime.

IMAGE

# Evaluation

Since this is a performance cliff that we didn't observe in any of our own
benchmarks ourselves, it's pointless to look at its effect on existing
benchmarks – there shouldn't and indeed there isn't any.

Instead, we are going to look at a micro-benchmark that came out of the original
report, one that simply renders a big artificial Tornado template.

All benchmarks were run 10 times in new processes. The means and standard
deviations of the benchmark runs are:

| Implementation   | Time taken (lower is better) |
|------------------|------------------------------|
|CPython 3.9.5     | 14.191 ± 0.348s              |
|PyPy3 without JIT | 59.479 ± 5.411s              |
|PyPy3 JIT old     | 14.469 ± 0.352s              |
|PyPy3 JIT new     |  4.892 ± 0.098s              |


<!--
1: /home/cfbolz/projects/small-commits-pypy/pypy/goal/pypy-c-38-jit-chunked-traces -jit off render.py
            Mean        Std.Dev.    Min         Median      Max
real        59.479      5.411       51.864      59.966      67.721      
user        59.395      5.383       51.821      59.859      67.585      
sys         0.058       0.034       0.020       0.056       0.108

1: pypy3 render.py
            Mean        Std.Dev.    Min         Median      Max
real        14.469      0.352       13.744      14.472      15.174      
user        14.399      0.359       13.671      14.402      15.126      
sys         0.050       0.034       0.024       0.042       0.148

Tracing:      	216	0.653033
Backend:      	24	0.003664
TOTAL:      		14.854610
ops:             	2217432
heapcached ops:  	701575
recorded ops:    	643513
  calls:         	60038
guards:          	330245
opt ops:         	1876
opt guards:      	465
opt guards shared:	237
forcings:        	0
abort: trace too long:	191
abort: compiling:	0
abort: vable escape:	0
abort: bad loop: 	0
abort: force quasi-immut:	1
nvirtuals:       	391
nvholes:         	122
nvreused:        	141
vecopt tried:    	0
vecopt success:  	0
Total # of loops:	17
Total # of bridges:	8
Freed # of loops:	5
Freed # of bridges:	5


1: /home/cfbolz/projects/small-commits-pypy/pypy/goal/pypy-c-38-jit-chunked-traces render.py
            Mean        Std.Dev.    Min         Median      Max
real        4.892       0.098       4.718       4.882       5.118       
user        4.807       0.097       4.644       4.797       5.022       
sys         0.067       0.019       0.040       0.070       0.096


Tracing:      	30	0.060128
Backend:      	25	0.033536
TOTAL:      		4.551791
ops:             	124584
heapcached ops:  	53962
recorded ops:    	33486
  calls:         	4389
guards:          	14061
opt ops:         	18922
opt guards:      	4281
opt guards shared:	2248
forcings:        	0
abort: trace too long:	4
abort: compiling:	0
abort: vable escape:	0
abort: bad loop: 	0
abort: force quasi-immut:	1
abort: segmenting trace:	5
nvirtuals:       	314
nvholes:         	90
nvreused:        	114
vecopt tried:    	0
vecopt success:  	0
Total # of loops:	14
Total # of bridges:	12
Freed # of loops:	0
Freed # of bridges:	0

-->


# Conclusion

In this post we've described a performance cliff in PyPy's JIT, that of really
big auto-generated functions which hit the trace limit without inlining, that we
still want to generate machine code for. We achieve this by chunking up the
trace into several smaller cases, which we added piece by piece. The work is a
tiny bit experimental still, but we will release it as part of the upcoming 3.8
beta release, to get some more experience with it.
