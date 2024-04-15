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

Vmprof's console output can already give some insights into where your code spends time, 
but it is far from showing all the information VMProf captures while profiling.

Created in the context of my bachelor's thesis, the vmprof-firefox-converter is a tool for viewing VMProf profiles with the Firefox profilers user interface. 
Here you can zoom into profiles, look at different visualizations like flamegraphs,
or even dive deeper into jitted functions.


# Usage

Profile your code with VMProf

`pypy -m vmprof -o profile.prof yourcode.py <args>`

Then convert the output file 

`pypy -m vmprofconvert -convert profile.prof`

Or let the converter take care of everything and run your code directly

`pypy -m vmprofconvert -run yourcode.py <args>`

Both `-convert` and `-run` will magically open the Firefox profiler in your browser

![firefox profiler](https://github.com/Cskorpion/vmprof-firefox-converter/blob/main/images/firefox.png?raw=true)

You may even create a sharable zip file that contains all the files necessary for investigating performance issues on another (person's) system. 

(This includes jitlog, pypylog, all the source files and of course the profile itself)

`pypy -m vmprofconvert --zip -run yourcode.py <args>`

# Getting started

Even though VMProf (and the converter) were created for profiling PyPy, you can also use them with CPython. 

You can get the converter from [GitHub](https://github.com/Cskorpion/vmprof-firefox-converter) 