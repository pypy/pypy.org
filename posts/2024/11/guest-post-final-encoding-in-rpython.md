<!--
.. type: text
.. title: Guest Post: Final Encoding in RPython Interpreters
.. slug: guest-post-final-encoding-in-rpython
.. date: 2024-11-11 17:08:36 UTC
.. tags: guestpost
.. category: 
.. link: 
.. description: 
.. type: text
.. author:
-->

# Guest Post: Final Encoding in RPython Interpreters

An RPython interpreter for a programming language generally does three or four
things, in order:

1. Read and parse input programs
1. Encode concrete syntax as abstract syntax
1. *Optionally*, optimize or reduce the abstract syntax
1. Evaluate the abstract syntax: read input data, compute, print output data,
   etc.

Today we'll look at abstract syntax. Most programming languages admit a
[concrete parse tree](https://en.wikipedia.org/wiki/Parse_tree) which is
readily abstracted to provide an [abstract syntax
tree](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST). The AST is
usually encoded with the *initial* style of encoding. An initial encoding can
be transformed into any other encoding for the same AST, looks like a
hierarchy of classes, and is implemented as a static structure on the heap.

In contrast, there is also a *final* encoding. A final encoding can be
transformed into by any other encoding, looks like an interface for the
actions of the interpreter, and is implemented as an unwinding structure on
the stack. From the RPython perspective, Python builtin modules like `os` or
`sys` are final encodings for features of the operating system; the underlying
implementation is different when translated or untranslated, but the interface
used to access those features does not change.

In RPython, an initial encoding is built from a hierarchy of classes. Each
class represents a type of tree nodes, corresponding to a parser production in
the concrete parse tree. Each class instance therefore represents an
individual tree node. The fields of a class, particularly those filled during
`.__init__()`, store pre-computed properties of each node; methods can be used
to compute node properties on demand. This seems like an obvious and simple
approach; what other approaches could there be? We need an example.

## Final Encoding of Brainfuck

We will consider [Brainfuck](https://esolangs.org/wiki/Brainfuck), a simple
Turing-complete programming language. An example Brainfuck program might be:

```brainfuck
[-]
```

This program is built from a loop and a decrement, and sets a cell to zero. In
an initial encoding which follows the [algebraic semantics of
Brainfuck](https://esolangs.org/wiki/Algebraic_Brainfuck), the program could
be expressed by applying class constructors to build a structure on the heap:

```python
Loop(Plus(-1))
```

A final encoding is similar, except that class constructors are replaced by
methods, the structure is built on the stack, and we are parameterized over
the choice of class:

```python
lambda cls: cls.loop(cls.plus(-1))
```

In ordinary Python, transforming between these would be trivial, and mostly is
a matter of passing around the appropriate class. Indeed, initial and final
encodings are equivalent; we'll return to that fact later. However, in RPython,
all of the types must line up, and classes must be determined before
translation. We'll need to monomorphize our final encodings, using some
RPython tricks later on. Before that, let's see what an actual Brainfuck
interface looks like, so that we can cover all of the difficulties with final
encoding.

Before we embark, please keep in mind that local code doesn't know what `cls`
is. There's no type-safe way to inspect an arbitrary semantic domain. In the
initial-encoded version, we can ask `isinstance(bf, Loop)` to see whether an
AST node is a loop, but there simply isn't an equivalent for final-encoded
ASTs. So, there is an implicit challenge to think about: how do we evaluate a
program in an arbitrary semantic domain? For bonus points, how do we optimize
a program without inspecting the types of its AST nodes?

What follows is a dissection of
[this](https://github.com/rpypkgs/rpypkgs/blob/d439d225b79ac82e009a5f1cd1c670f00356464c/bf/bf.py)
module at the given revision. Readers may find it satisfying to read the
entire interpreter top to bottom first; it is less than 300 lines.

### Core Functionality

Final encoding is given as methods on an interface. These five methods
correspond precisely to the summands of the algebra of Brainfuck.

```python
class BF(object):
    # Other methods elided
    def plus(self, i): pass
    def right(self, i): pass
    def input(self): pass
    def output(self): pass
    def loop(self, bfs): pass
```

Note that the `.loop()` method takes another program as an argument.
Initial-encoded ASTs have other initial-encoded ASTs as fields on class
instances; final-encoded ASTs have other final-encoded ASTs as parameters
to interface methods.

We're using a class to implement this functionality. Later, we'll treat it as
a mixin, rather than a superclass, to avoid typing problems.

### Monoid

In order to optimize input programs, we'll need to represent the underlying
[monoid](https://en.wikipedia.org/wiki/Monoid) of Brainfuck programs. To do
this, we add the signature for a monoid:

```python
class BF(object):
    # Other methods elided
    def unit(self): pass
    def join(self, l, r): pass
```

This is technically a [unital
magma](https://en.wikipedia.org/wiki/Magma_(algebra)), since RPython doesn't
support algebraic laws, but we will enforce the algebraic laws later on during
optimization. We also want to make use of the folklore that [free
monoids](https://en.wikipedia.org/wiki/Free_monoid) are lists, allowing
callers to pass a list of actions which we'll reduce with recursion:

```python
class BF(object):
    # Other methods elided
    def joinList(self, bfs):
        if not bfs: return self.unit()
        elif len(bfs) == 1: return bfs[0]
        elif len(bfs) == 2: return self.join(bfs[0], bfs[1])
        else:
            i = len(bfs) >> 1
            return self.join(self.joinList(bfs[:i]), self.joinList(bfs[i:]))
```

`.joinList()` is a little bulky to implement, but Wirth's principle applies:
the interpreter is shorter with it than without it.

### Idioms

Finally, our interface includes a few high-level idioms, like the zero program
shown earlier, which are defined in terms of low-level behaviors. In an
initial encoding, these could be defined as module-level functions; here, we
define them on the mixin class `BF`.

```python
class BF(object):
    # Other methods elided
    def zero(self): return self.loop(self.plus(-1))
    def move(self, i): return self.scalemove(i, 1)
    def move2(self, i, j): return self.scalemove2(i, 1, j, 1)
    def scalemove(self, i, s):
        return self.loop(self.joinList([
            self.plus(-1), self.right(i), self.plus(s), self.right(-i)]))
    def scalemove2(self, i, s, j, t):
        return self.loop(self.joinList([
                self.plus(-1), self.right(i), self.plus(s), self.right(j - i),
                self.plus(t), self.right(-j)]))
```

## Interface-oriented Architecture

### Applying Interfaces

Now, we hack at RPython's object model until everything translates. First,
consider the task of pretty-printing. For Brainfuck, we'll simply regurgitate
the input program as a Python string:

```python
class AsStr(object):
    import_from_mixin(BF)
    def unit(self): return ""
    def join(self, l, r): return l + r
    def plus(self, i): return '+' * i if i > 0 else '-' * -i
    def right(self, i): return '>' * i if i > 0 else '<' * -i
    def loop(self, bfs): return '[' + bfs + ']'
    def input(self): return ','
    def output(self): return '.'
```

Via `rlib.objectmodel.import_from_mixin`, no stressing with covariance of
return types is required. Instead, we shift from a Java-esque view of classes
and objects, to an OCaml-ish view of prebuilt classes and constructors.
`AsStr` is monomorphic, and any caller of it will have to create their own
covariance somehow. For example, here are the first few lines of the parsing
function:

```python
@specialize.argtype(1)
def parse(s, domain):
    ops = [domain.unit()]
    # Parser elided to preserve the reader's attention
```

By invoking `rlib.objectmodel.specialize.argtype`, we make copies of the
parsing function, up to one per call site, based on our choice of semantic
domain. [Oleg](https://okmij.org/ftp/tagless-final/) calls these "symantics"
but I prefer "domain" in code. Also, note how the parsing stack starts with
the unit of the monoid, which corresponds to the empty input string; the
parser will repeatedly use the monoidal join to build up a parsed expression
without inspecting it. Here's a small taste of that:

```python
while i < len(s):
    char = s[i]
    if char == '+': ops[-1] = domain.join(ops[-1], domain.plus(1))
    elif char == '-': ops[-1] = domain.join(ops[-1], domain.plus(-1))
    # and so on
```

The reader may feel justifiably mystified; what breaks if we don't add these
magic annotations? Well, the translator will throw `UnionError` because the
low-level types don't match. RPython only wants to make one copy of functions
like `parse()` in its low-level representation, and each copy of `parse()`
will be compiled to monomorphic machine code. In this interpreter, in order to
support parsing to an optimized string and also parsing to an evaluator, we
need two copies of `parse()`. **It is okay to not fully understand this at
first.**

### Composing Interfaces

Earlier, we noted that an interpreter can optionally optimize input programs
after parsing. To support this, we'll precompose a [peephole
optimizer](https://en.wikipedia.org/wiki/Peephole_optimization) onto an
arbitrary domain. We could also postcompose with a parser instead, but that
sounds more difficult. Here are the relevant parts:

```python
def makePeephole(cls):
    domain = cls()
    def stripDomain(bfs): return domain.joinList([t[0] for t in bfs])
    class Peephole(object):
        import_from_mixin(BF)
        def unit(self): return []
        def join(self, l, r): return l + r
        # Actual definition elided... for now...
    return Peephole, stripDomain
```

Don't worry about the actual optimization yet. What's important here is the
pattern of initialization of semantic domains. `makePeephole` is an
[SML](https://en.wikipedia.org/wiki/Standard_ML)-style functor on semantic
domains: given a final encoding of Brainfuck, it produces another final
encoding of Brainfuck which incorporates optimizations. The helper
`stripDomain` is a finalizer which performs the extraction from the
optimizer's domain to the underlying `cls` that was passed in at translation
time. For example, let's optimize pretty-printing:

```python
AsStr, finishStr = makePeephole(AsStr)
```

Now, it only takes one line to parse and print an optimized AST without ever
building it on the heap. To be pedantic, fragments of the output string will
be heap-allocated, but the AST's node structure will only ever be
stack-allocated. Further, to be shallow, the parser is written to prevent
malicious input from causing a stack overflow, and this forces it to maintain
a heap-allocated RPython list of intermediate operations inside loops.

```python
print finishStr(parse(text, AsStr()))
```

## Performance

But is it fast? Yes. It's faster than the prior version, which was
initial-encoded, and also faster than Andrew Brown's classic version ([part
1](https://pypy.org/posts/2011/04/tutorial-writing-interpreter-with-pypy-3785910476193156295.html),
[part
2](https://pypy.org/posts/2011/04/tutorial-part-2-adding-jit-8121732841568309472.html)).
Since Brown's interpreter does not perform much optimization, we will focus on
how final encoding can outperform initial encoding.

### JIT

First, why is it faster than the same interpreter with initial encoding? Well,
it still has initial encoding from the JIT's perspective! There is an `Op`
class with a hierarchy of subclasses implementing individual behaviors. A
sincere tagless-final student, or those who remember [Stop Writing Classes
(2012, Pycon
US)](https://pyvideo.org/pycon-us-2012/stop-writing-classes.html), will
recognize that the following classes could be plain functions, and should
think of the classes as a concession to RPython's lack of support for lambdas
with closures rather than an initial encoding. We aren't ever going to
directly typecheck any `Op`, but the JIT will generate typechecking guards
anyway, so we effectively get a fully-promoted AST inlined into each JIT
trace. First, some simple behaviors:

```python
class Op(object): _immutable_ = True

class _Input(Op):
    _immutable_ = True
    def runOn(self, tape, position):
        tape[position] = ord(os.read(0, 1)[0])
        return position
Input = _Input()

class _Output(Op):
    _immutable_ = True
    def runOn(self, tape, position):
        os.write(1, chr(tape[position]))
        return position
Output = _Output()

class Add(Op):
    _immutable_ = True
    _immutable_fields_ = "imm",
    def __init__(self, imm): self.imm = imm
    def runOn(self, tape, position):
        tape[position] += self.imm
        return position
```

The JIT does technically have less information than before; it no longer knows
that a sequence of immutable operations is immutable enough to be worth
unrolling, but a bit of `rlib.jit.unroll_safe` fixes that:

```python
class Seq(Op):
    _immutable_ = True
    _immutable_fields_ = "ops[*]",
    def __init__(self, ops): self.ops = ops
    @unroll_safe
    def runOn(self, tape, position):
        for op in self.ops: position = op.runOn(tape, position)
        return position
```

Finally, the JIT entry point is at the head of each loop, just like with prior
interpreters. Since Brainfuck doesn't support mid-loop jumps, there's no
penalty for only allowing merge points at the head of the loop.

```python
class Loop(Op):
    _immutable_ = True
    _immutable_fields_ = "op",
    def __init__(self, op): self.op = op
    def runOn(self, tape, position):
        op = self.op
        while tape[position]:
            jitdriver.jit_merge_point(op=op, position=position, tape=tape)
            position = op.runOn(tape, position)
        return position
```

That's the end of the implicit challenge. There's no secret to it; just
evaluate the AST. Here's part of the semantic domain for evaluation, as well
as the "functor" to optimize it. In `AsOps.join()` are the *only*
`isinstance()` calls in the entire interpreter! This is acceptable because
`Seq` is effectively a type wrapper for an RPython list, so that a list of
operations is also an operation; its list is initial-encoded and available for
inspection.

```python
class AsOps(object):
    import_from_mixin(BF)
    def unit(self): return Shift(0)
    def join(self, l, r):
        if isinstance(l, Seq) and isinstance(r, Seq):
            return Seq(l.ops + r.ops)
        elif isinstance(l, Seq): return Seq(l.ops + [r])
        elif isinstance(r, Seq): return Seq([l] + r.ops)
        return Seq([l, r])
    # Other methods elided!

AsOps, finishOps = makePeephole(AsOps)
```

And finally here is the actual top-level code to evaluate the input program.
As before, once everything is composed, the actual invocation only takes one
line.

```python
tape = bytearray("\x00" * cells)
finishOps(parse(text, AsOps())).runOn(tape, 0)
```

### Peephole Optimization

Our peephole optimizer is an [abstract
interpreter](https://en.wikipedia.org/wiki/Abstract_interpretation) with one
instruction of lookahead/rewrite buffer. It implements the aforementioned
algebraic laws of the Brainfuck monoid. It also implements idiom recognition
for loops. First, the abstract interpreter. The abstract domain has six
elements:

```python
class AbstractDomain(object): pass
meh, aLoop, aZero, theIdentity, anAdd, aRight = [AbstractDomain() for _ in range(6)]
```

We'll also tag everything with an integer, so that `anAdd` or `aRight` can be
exact annotations. *This* is the actual `Peephole.join()` method:

```python
def join(self, l, r):
    if not l: return r
    rv = l[:]
    bfHead, adHead, immHead = rv.pop()
    for bf, ad, imm in r:
        if ad is theIdentity: continue
        elif adHead is aLoop and ad is aLoop: continue
        elif adHead is theIdentity:
            bfHead, adHead, immHead = bf, ad, imm
        elif adHead is anAdd and ad is aZero:
            bfHead, adHead, immHead = bf, ad, imm
        elif adHead is anAdd and ad is anAdd:
            immHead += imm
            if immHead: bfHead = domain.plus(immHead)
            elif rv: bfHead, adHead, immHead = rv.pop()
            else:
                bfHead = domain.unit()
                adHead = theIdentity
        elif adHead is aRight and ad is aRight:
            immHead += imm
            if immHead: bfHead = domain.right(immHead)
            elif rv: bfHead, adHead, immHead = rv.pop()
            else:
                bfHead = domain.unit()
                adHead = theIdentity
        else:
            rv.append((bfHead, adHead, immHead))
            bfHead, adHead, immHead = bf, ad, imm
    rv.append((bfHead, adHead, immHead))
    return rv
```

If this were to get much longer, then [implementing a
DSL](https://pypy.org/posts/2024/10/jit-peephole-dsl.html) would be worth it,
but this is a short-enough method to inline. The abstract interpretation is
assumed by induction for the left-hand side of the join, save for the final
instruction, which is loaded into a rewrite register. Each instruction on the
right-hand side is inspected exactly once. The logic for `anAdd` followed by
`anAdd` is exactly the same as for `aRight` followed by `aRight` because they
both have underlying [Abelian
groups](https://en.wikipedia.org/wiki/Abelian_group) given by the integers.
The rewrite register is carefully pushed onto and popped off from the
left-hand side in order to cancel out `theIdentity`, which itself is merely a
unifier for `anAdd` or `aRight` of 0.

Note that we generate a lot of garbage. For example, parsing a string of *n*
'+' characters will cause the peephole optimizer to allocate *n* instances of
the underlying `domain.plus()` action, from `domain.plus(1)` up to
`domain.plus(n)`. An older initial-encoded version of this interpreter used
[hash consing](https://en.wikipedia.org/wiki/Hash_consing) to avoid ever
building an op more than once, even loops. It appears more efficient to
generate lots of immutable garbage than to repeatedly hash inputs and search
mutable hash tables, at least for optimizing Brainfuck incrementally during
parsing.

Finally, let's look at idiom recognition. RPython lists are initial-coded, so
we can dispatch based on the length of the list, and then inspect the abstract
domains of each action.

```python
def isConstAdd(bf, i): return bf[1] is anAdd and bf[2] == i

def oppositeShifts(bf1, bf2):
    return bf1[1] is bf2[1] is aRight and bf1[2] == -bf2[2]

def oppositeShifts2(bf1, bf2, bf3):
    return (bf1[1] is bf2[1] is bf3[1] is aRight and
            bf1[2] + bf2[2] + bf3[2] == 0)

def loop(self, bfs):
    if len(bfs) == 1:
        bf, ad, imm = bfs[0]
        if ad is anAdd and imm in (1, -1):
            return [(domain.zero(), aZero, 0)]
    elif len(bfs) == 4:
        if (isConstAdd(bfs[0], -1) and
            bfs[2][1] is anAdd and
            oppositeShifts(bfs[1], bfs[3])):
            return [(domain.scalemove(bfs[1][2], bfs[2][2]), aLoop, 0)]
        if (isConstAdd(bfs[3], -1) and
            bfs[1][1] is anAdd and
            oppositeShifts(bfs[0], bfs[2])):
            return [(domain.scalemove(bfs[0][2], bfs[1][2]), aLoop, 0)]
    elif len(bfs) == 6:
        if (isConstAdd(bfs[0], -1) and
            bfs[2][1] is bfs[4][1] is anAdd and
            oppositeShifts2(bfs[1], bfs[3], bfs[5])):
            return [(domain.scalemove2(bfs[1][2], bfs[2][2],
                                       bfs[1][2] + bfs[3][2],
                                       bfs[4][2]), aLoop, 0)]
        if (isConstAdd(bfs[5], -1) and
            bfs[1][1] is bfs[3][1] is anAdd and
            oppositeShifts2(bfs[0], bfs[2], bfs[4])):
            return [(domain.scalemove2(bfs[0][2], bfs[1][2],
                                       bfs[0][2] + bfs[2][2],
                                       bfs[3][2]), aLoop, 0)]
    return [(domain.loop(stripDomain(bfs)), aLoop, 0)]
```

This ends the bonus question. How do we optimize an unknown semantic domain?
We must maintain an abstract context which describes elements of the domain.
In initial encoding, we ask an AST about itself. In final encoding, we already
know everything relevant about the AST.

The careful reader will see that I didn't really answer that opening question
in the JIT section. Because the JIT still ranges over the same operations as
before, it can't really be slower; but why is it now faster? Because the
optimizer is now slightly better in a few edge cases. It performs the same
optimizations as before, but the rigor of abstract interpretation causes it to
emit slightly better operations to the JIT backend.

Concretely, improving the optimizer can shorten pretty-printed programs. The
[Busy Beaver Gauge](https://bbgauge.info/) measures the length of programs
which search for solutions to mathematical problems. After implementing and
debugging the final-encoded interpreter, I found that two of my entries on the
[Busy Beaver Gauge for Brainfuck](https://bbgauge.info/brainfuck.html) had
become shorter by about 2%. (Most other entries are already hand-optimized
according to the standard algebra and have no optimization opportunities.)

## Discussion

Given that initial and final encodings are equivalent, and noting that
RPython's toolchain is written to prefer initial encodings, what did we
actually gain? Did we gain anything?

One obvious downside to final encoding in RPython is interpreter size. The
example interpreter shown here is a rewrite of an initial-encoded interpreter
which can be seen
[here](https://github.com/rpypkgs/rpypkgs/blob/659c8a26d428a1e04fdff614b28e464a50d4647b/bf/bf.py)
for comparison. Final encoding adds about 20% more code in this case.

Final encoding is not necessarily more code than initial encoding, though. All
AST encodings in interpreters are subject to the [Expression
Problem](https://en.wikipedia.org/wiki/Expression_problem), which states that
there is generally a quadratic amount of code required to implement multiple
behaviors for an AST with multiple types of nodes; specifically, *n* behaviors
for *m* types of nodes require *n* × *m* methods. Initial encodings improve the
cost of adding new types of nodes; final encodings improve the cost of adding
new behaviors. Final encoding may tend to win in large codebases for mature
languages, where the language does not change often but new behaviors are added
frequently and maintained for long periods.

Optimizations in final encoding require a bit of planning. The
abstract-interpretation approach is solid but relies upon the monoid and its
algebraic laws. In the worst case, an entire class hierarchy could be required
to encode the abstraction.

It is remarkable to find **a 2% improvement in residual program size** merely
by reimplementing an optimizer as an abstract interpreter respecting the
algebraic laws. This could be the most important lesson for compiler
engineers, if it happens to generalize.

Final encoding was popularized via the tagless-final movement. A "tag", in
this jargon, is a runtime identifier for an object's type or class; a tagless
encoding effectively doesn't allow `isinstance()` at all. In the above
presentation, tags could be hacked in, but were not materially relevant to
most steps. Tags were required for the final evaluation step, though, and the
tagless-final insight is that certain type systems can express type-safe
evaluation without those tags. We won't go further in this direction because
tags also communicate valuable information to the JIT.

### Summarizing Table

Initial Encoding | Final Encoding
---|---
hierarchy of classes | signature of interfaces
class constructors | method calls
built on the heap | built on the stack
traversals allocate stack | traversals allocate heap
tags are available with `isinstance()` | tags are only available through hacks
cost of adding a new AST node: one class | cost of adding a new AST node: one method on every other class
cost of adding a new behavior: one method on every other class | cost of adding a new behavior: one class
