<!--
.. title: vmprof-firefox-converter
.. slug: 
.. date: 2024-04-15 13:49:00 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: text
.. author: Christoph Jung
-->

# Introduction

If you ever wanted to profile your Python code on PyPy, you probably came across VMProf.

VMProf's console output can already give some insights into where your code spends time, 
but it is far from showing all the information captured while profiling.

There have been some tools arround to visualize VMProf's output,
but since the vmprof.com user interface is no longer available and vmprof-server is not as easy to use, you may want to take a look at a local viewer/tool/converter.
Those so far could give you some general visualizations of your profile. Unfortunately, those tools cannot show any PyPy related context like PyPyLog or jitlog.

To bring all of those features together in one local tool, you may take a look at the vmprof-firefox-converter.

Created in the context of my bachelor's thesis, the vmprof-firefox-converter is a tool for analyzing VMProf profiles with the Firefox profiler user interface. 
The Firefox profiler offers a timeline where you can zoom into profiles and work with different visualizations like a flame graph or stack chart.
To understand why there is time spent inside a function, you can revisit the source code and even dive into the intermediate representation of functions executed by PyPy's just-in-time compiler.
By having a look at the PyPyLog track, it is easy to see when PyPy was inside the interpreter, JIT or GC throughout the profiling time.

# Profiling word count

TODO

# Usage

Profile your code with VMProf

`pypy -m vmprof -o profile.prof yourcode.py <args>`

Then convert the output file 

`pypy -m vmprofconvert -convert profile.prof`

Or let the converter take care of everything and run your code directly

`pypy -m vmprofconvert -run yourcode.py <args>`

Both `-convert` and `-run` will open the Firefox profiler in your browser

![firefox profiler](https://github.com/Cskorpion/vmprof-firefox-converter/blob/main/images/firefox.png?raw=true)

You may even create a sharable zip file that contains all the files necessary for investigating performance issues on another (person's) system. 

(This includes jitlog, pypylog, all the source files and of course the profile itself)

`pypy -m vmprofconvert --zip -run yourcode.py <args>`

# Getting started

Even though VMProf and the converter were created for profiling PyPy, you can also use them with CPython. 

You can get the converter from [GitHub](https://github.com/Cskorpion/vmprof-firefox-converter) 