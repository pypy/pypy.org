.. title: Allocation Removal in the Toy Optimizer
.. slug: toy-optimizer-allocation-removal
.. date: 2022-07-30 15:00:00 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

In the previous_ blog post of this serious I showed the complete code for
writing a toy one-pass optimizer that does constant folding, common
subexpression elimination and strength reduction. All those optimizations are in
some way relatively straightforward in this really minimal form. So in this
second post, I want to show a more interesting optimization pass which removes
allocations that never escape. The basic optimization framework is the same, we
will use the same datastructures for intermediate representation and also keep
using the same union find data structure to store equivalences between IR
operations. Here's the code:

.. code:: python

    import pytest
    import re
    from typing import Optional, Any


    class Value:
        def find(self):
            raise NotImplementedError("abstract")

        def _set_forwarded(self, value):
            raise NotImplementedError("abstract")


    class Operation(Value):
        def __init__(
            self, name: str, args: list[Value]
        ):
            self.name = name
            self.args = args
            self.forwarded = None
            self.info = None

        def __repr__(self):
            return (
                f"Operation({self.name}, "
                f"{self.args}, {self.forwarded}, "
                f"{self.info})"
            )

        def find(self) -> Value:
            op = self
            while isinstance(op, Operation):
                next = op.forwarded
                if next is None:
                    return op
                op = next
            return op

        def arg(self, index):
            return self.args[index].find()

        def make_equal_to(self, value: Value):
            self.find()._set_forwarded(value)

        def _set_forwarded(self, value: Value):
            self.forwarded = value


    class Constant(Value):
        def __init__(self, value: Any):
            self.value = value

        def __repr__(self):
            return f"Constant({self.value})"

        def find(self):
            return self

        def _set_forwarded(self, value: Value):
            assert (
                isinstance(value, Constant)
                and value.value == self.value
            )

    class Block(list):
        def opbuilder(opname):
            def wraparg(arg):
                if not isinstance(arg, Value):
                    arg = Constant(arg)
                return arg
            def build(self, *args):
                # construct an Operation, wrap the
                # arguments in Constants if necessary
                op = Operation(opname,
                    [wraparg(arg) for arg in args])
                # add it to self, the basic block
                self.append(op)
                return op
            return build

        # a bunch of operations we support
        add = opbuilder("add")
        mul = opbuilder("mul")
        getarg = opbuilder("getarg")
        dummy = opbuilder("dummy")
        lshift = opbuilder("lshift")
        # some new one for this post
        alloc = opbuilder("alloc")
        load = opbuilder("load")
        store = opbuilder("store")
        escape = opbuilder("escape")

    def bb_to_str(bb: Block, varprefix: str = "var"):
        def arg_to_str(arg: Value):
            if isinstance(arg, Constant):
                return str(arg.value)
            else:
                return varnames[arg]

        varnames = {}
        res = []
        for index, op in enumerate(bb):
            var = f"{varprefix}{index}"
            varnames[op] = var
            arguments = ", ".join(
                arg_to_str(op.arg(i))
                    for i in range(len(op.args))
            )
            strop = f"{var} = {op.name}({arguments})"
            res.append(strop)
        return "\n".join(res)

There are two changes to the code from the last post: ``Operation`` instances
have a new ``.info`` field, which is set to ``None`` by default. We will learn
how the info field is used a bit further down. Also, we define some new
operations.


Interpreter
=============

In this post we will mainly concern ourselves with optimizing
programs that allocate memory. We assume that our language is garbage collected
and memory safe. The new operations that we will optimize are ``alloc``
(allocates a new object), ``store`` (stores a value into a fixed field of an
object), ``load`` (loads the value from a field in the object).

Here's a simple program that uses these operations::

    var0 = getarg(0)
    obj0 = alloc()
    store(obj0, 0, var0)
    var1 = load(obj0, 0)
    escape(var1)

The code allocates a new object, stores ``var0`` into field ``0`` of the object,
the loads the same field and escapes the result of the load.

We are leaving a lot of details of a "real" system here, usually an ``alloc``
operation would get some extra information, for example the type of the freshly
allocated object or at least its size.

To understand the semantics of the new allocations a bit better, let's actually
write an interpreter for basic blocks, supporting only ``getarg``, ``alloc``,
``store``, ``load``, ``escape``:

.. code:: python

    def test_interpret():
        bb = Block()
        var0 = bb.getarg(0)
        obj = bb.alloc()
        sto = bb.store(obj, 0, var0)
        var1 = bb.load(obj, 0)
        bb.escape(var1)
        assert interpret(bb, 17) == 17

    class Object:
        def __init__(self):
            self.contents: dict[int, Any] = {}

        def store(self, idx : int, value : Any):
            self.contents[idx] = value

        def load(self, idx : int):
            return self.contents[idx]

    def get_num(op, index=1):
        assert isinstance(op.arg(index), Constant)
        return op.arg(index).value

    def interpret(bb : Block, *args : tuple[Any]):
        def argval(op, i):
            arg = op.arg(i)
            if isinstance(arg, Constant):
                return arg.value
            else:
                assert isinstance(arg, Operation)
                return arg.info

        for index, op in enumerate(bb):
            if op.name == "getarg":
                res = args[get_num(op, 0)]
            elif op.name == "alloc":
                res = Object()
            elif op.name == "load":
                res = argval(op, 0).load(
                    get_num(op))
            elif op.name == "store":
                argval(op, 0).store(
                    get_num(op), argval(op, 2))
                # no result, only side effect
                continue
            elif op.name == "escape":
                return argval(op, 0)
            op.info = res

The interpreter  walks the operations of a block, executes each one in turn. It
uses the ``info`` field to store the result of each already executed
``Operation``. In this interpreter sketch we stop at the first ``escape`` that
we execute and return its argument.

Objects in the interpreter are represented using a class ``Object``, which
stores the object's field into a Python dictionary.

Motivation: Removing Allocations
=================================

In many programs, some allocated objects don't live for very long and have a
completely predictable lifetime. They get allocated, used for a while, and then
there is no way to reference them any more, so the garbage collector will
reclaim them. The very first example block had such an allocation::

    var0 = getarg(0)
    obj0 = alloc()
    store(obj0, 0, var0)
    var1 = load(obj0, 0)
    escape(var1)

Here ``obj0`` is written to, then read from, and then it's no longer used. We
want to optimize such programs to remove this ``alloc`` operation. The optimized
version of this program would look like this::

    var0 = getarg(0)
    escape(var0)

The ``alloc``, ``store`` and ``load`` operations have been completely removed.
This is a pretty important optimizations for PyPy's JIT, and it is not a lot of
code to implement it! However, understanding all the corner cases of the
optimization and making sure that the resulting program behave correctly is not
completely trivial. Therefore we will develop the optimization step by step, in
a test driven fashion: I will start each section with a new test that shows a
bug in the version of the optimization that we have so far.

Version 1: Naive Attempt
========================

Let's start in a really naive way. Here's the first test we would like to
pass, using the example program above:

.. code:: python

    def test_remove_unused_allocation():
        bb = Block()
        var0 = bb.getarg(0)
        obj = bb.alloc()
        sto = bb.store(obj, 0, var0)
        var1 = bb.load(obj, 0)
        bb.escape(var1)
        opt_bb = optimize_alloc_removal(bb)
        # the virtual object looks like this:
        #  obj
        # ┌──────────┐
        # │ 0: var0  │
        # └──────────┘
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = escape(optvar0)"""


We will define a class ``VirtualObject`` that is basically identical to
``Object`` above. But it will not be used during the interpreter, instead we
will use it during optimization.

.. code:: python

    class VirtualObject:
        def __init__(self):
            self.contents: dict[int, Value] = {}

        def store(self, idx, value):
            self.contents[idx] = value

        def load(self, idx):
            return self.contents[idx]

The structure of the optimizer is going to be like those in the first blog post.
The optimizer makes a single pass over all operations. It removes some and
emits others.

This first version of the allocation removal optimizer is going to be extremely
optimistic. It simply assumes that *all* the allocations in the program can be
optimized away. That is obviously not realistic in practice, we will have to
refine this approach later, but it's a good way to start. So whenever the
optimizer sees an ``alloc`` operation, it removes it and creates a
``VirtualObject`` object which stores the information that is known during
optimization about the result of the ``alloc``. Like in the interpreter, the
``VirtualObject`` is stored in the ``.info`` field of the ``Operation`` instance
that represents the ``alloc``.

When the optimizer sees a ``store`` operation, it will also remove it and
instead put execute the store by calling the ``VirtualObject.store`` method.
Here is one important difference between the interpreter and the optimizer: In
the interpreter, the values that were stored into an ``Object`` (and thus
put into the object's ``.contents`` dictionary) where runtime values, for
example integers or other objects. In the optimizer however, the
fields of the ``VirtualObject`` store ``Value`` instances, either ``Constant``
instances or ``Operation`` instances.

When the optimizer sees a ``load`` operation, it *also* removes it, and replaces
the ``load`` with the ``Operation`` (or ``Constant``) that is stored in the
``VirtualObject`` at that point.

.. code:: python

    def optimize_alloc_removal(bb):
        opt_bb = Block()
        for op in bb:
            if op.name == "alloc":
                op.info = VirtualObject()
                continue
            if op.name == "load":
                info = op.arg(0).info
                field = get_num(op)
                op.make_equal_to(info.load(field))
                continue
            if op.name == "store":
                info = op.arg(0).info
                field = get_num(op)
                info.store(field, op.arg(2))
                continue
            opt_bb.append(op)
        return opt_bb

So this is the first version of the optimization! It doesn't handle all kinds of
difficult cases, and we'll have to do something about its optimism first.
However, we can write a slightly more complicated test with two allocations, and
object pointing to the other. It works correctly too, both allocations are
removed.

.. code:: python

    def test_remove_two_allocations():
        bb = Block()
        var0 = bb.getarg(0)
        obj0 = bb.alloc()
        sto1 = bb.store(obj0, 0, var0)
        obj1 = bb.alloc()
        sto2 = bb.store(obj1, 0, obj0)
        var1 = bb.load(obj1, 0)
        var2 = bb.load(var1, 0)
        bb.escape(var2)
        # the virtual objects look like this:
        #  obj0
        # ┌──────┐
        # │ 0: ╷ │
        # └────┼─┘
        #      │
        #      ▼
        #     obj1
        #   ┌─────────┐
        #   │ 0: var0 │
        #   └─────────┘
        # therefore
        # var1 is the same as obj0
        # var2 is the same as var0
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = escape(optvar0)"""



Version 2: Re-Materialize Allocations
======================================

The most obvious problem that we need to fix first is the assumption that every
allocation can be removed. So far we only looked at small programs that allocate
some objects, stores into and loads from them, and then forgets the objects. In
this simple case removing the allocations is fine. Storing one object whose
allocation we remove into another such object is fine too.

To make it easier to talk about how the optimizer operates, let's introduce
some terminology (this is how PyPy uses the terminology, not really used
consistently by other projects as far as I know). As already seen by the choice
of the class name ``VirtualObject``, we will call an object **virtual** if the
optimizer has optimized away the ``alloc`` operation that creates the object.
Other objects are equivalently **not virtual**, for example those that have
existed before we enter the current code block.

To remove the assumption of the first version of the optimizer that every
allocation can be removed, we will use a simple heuristic. The heuristic is as
follows: if a reference to a virtual object ``a`` is stored into an object ``b``
that is not virtual, then ``a`` will also stop being virtual. If an object ``a``
that was virtual stops being virtual, we say that it **escapes**.

The simplest test case for this happening looks like this:

.. code:: python

    def test_materialize():
        bb = Block()
        var0 = bb.getarg(0)
        obj = bb.alloc()
        sto = bb.store(var0, 0, obj)
        opt_bb = optimize_alloc_removal(bb)
        #  obj is virtual, without any fields
        # ┌───────┐
        # │ empty │
        # └───────┘
        # and then we store into field 0 of var0 a
        # reference to obj. since var0 is not virtual,
        # obj must escape, so we have to put it back
        # into the optimized basic block
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = store(optvar0, 0, optvar1)"""
        # so far, fails like this:
        # the line:
        # info.store(field, op.arg(2))
        # produces an AttributeError because info
        # is None

If the optimizer reaches a point where a virtual object escapes (like the
``store`` operation in the test, the optimizer has already removed the ``alloc``
operation that created the virtual object. If the object escapes, we don't want
to go back in the operations list and re-insert the alloc operation, we would
have to do a lot of work. Instead, we re-insert the ``alloc`` operation that will
recreate the virtual object at the point of escape using a helper function
``materialize``.

.. code:: python
    :emphasize-lines: 1-8,23-28

    def materialize(opt_bb, value: Operation) -> None:
        assert not isinstance(value, Constant)
        assert isinstance(value, Operation)
        info = value.info
        assert isinstance(info, VirtualObject)
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)

I've added a number of fairly strong assertions to ``materialize`` to encode our
current assumptions about the situations in which it expects to be called. We
will remove some of them later as we generalize the code.

Now that we have ``materialize`` we need to change ``optimize_alloc_removal`` to
recognize the case of storing a virtual object into a non-virtual one. We can
recognize ``Operation`` instances that produced a virtual object by looking at
their ``.info`` field. If it is ``None``, the object is not virtual, otherwise
it is. If we store something into a virtual object, we leave the code as above.
If we store a virtual object into an object that is not virtual, we will first
materialize the virtual object, and then emit the store.

.. code:: python
    :emphasize-lines: 14-23

    def optimize_alloc_removal(bb):
        opt_bb = Block()
        for op in bb:
            if op.name == "alloc":
                op.info = VirtualObject()
                continue
            if op.name == "load":
                info = op.arg(0).info
                field = get_num(op)
                op.make_equal_to(info.load(field))
                continue
            if op.name == "store":
                info = op.arg(0).info
                if info: # virtual
                    field = get_num(op)
                    info.store(field, op.arg(2))
                    continue
                else: # not virtual
                    # first materialize the
                    # right hand side
                    materialize(opt_bb, op.arg(2))
                    # then emit the store via
                    # the general path below
            opt_bb.append(op)
        return opt_bb

This is the general idea, and it is enough to pass ``test_materialize``. But of
course there are still a lot of problems that we now need to solve.


Version 3: Don't Materialize Twice
===================================

The first problem is the fact that after we materialize a virtual object, it is
no longer virtual. So if it escapes a second time, it should *not* be
materialized a second time. A test for that case could simply repeat the
``store`` operation:

.. code:: python

    def test_dont_materialize_twice():
        # obj is again an empty virtual object, and we
        # store it into var0 *twice*. this should
        # only materialize it once, though!
        bb = Block()
        var0 = bb.getarg(0)
        obj = bb.alloc()
        sto0 = bb.store(var0, 0, obj)
        sto1 = bb.store(var0, 0, obj)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = store(optvar0, 0, optvar1)
    optvar3 = store(optvar0, 0, optvar1)"""
        # fails so far! the operations that we get
        # at the moment are:
        # optvar0 = getarg(0)
        # optvar1 = alloc()
        # optvar2 = store(optvar0, 0, optvar1)
        # optvar3 = alloc()
        # optvar4 = store(optvar0, 0, optvar3)
        # ie the object is materialized twice
        # which is incorrect

We solve the problem by setting the ``.info`` field of an object that we
materialize to ``None``. After all, a materialized object is no longer virtual.


.. code:: python
    :emphasize-lines: 5-6,8,10-11

    def materialize(opt_bb, value: Operation) -> None:
        assert not isinstance(value, Constant)
        assert isinstance(value, Operation)
        info = value.info
        if info is None:
            return # already materialized
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)
        # but only once
        value.info = None

    # optimize_alloc_removal unchanged

This fixes the problem, only one ``alloc`` is created. This fix also allows
another test case to pass, one where we store a non-virtual into another
non-virtual, code which we cannot optimize at all:

.. code:: python

    def test_materialize_non_virtuals():
        # in this example we store a non-virtual var1
        # into another non-virtual var0
        # this should just lead to no optmization at
        # all
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.getarg(1)
        sto = bb.store(var0, 0, var1)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = getarg(1)
    optvar2 = store(optvar0, 0, optvar1)"""


Version 4: Materialization of Constants
=========================================

Another straightforward extension is to support materializing constants. A
constant is never virtual, so materializing it should do nothing.

.. code:: python

    def test_materialization_constants():
        # in this example we store the constant 17
        # into the non-virtual var0
        # this should just lead to no optmization at
        # all
        bb = Block()
        var0 = bb.getarg(0)
        sto = bb.store(var0, 0, 17)
        opt_bb = optimize_alloc_removal(bb)
        # the previous line fails so far, triggering
        # the assert:
        # assert not isinstance(value, Constant)
        # in materialize
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = store(optvar0, 0, 17)"""

To implement that case, we check for ``value`` being a constant and return
early:

.. code:: python
    :emphasize-lines: 2-3

    def materialize(opt_bb, value: Operation) -> None:
        if isinstance(value, Constant):
            return
        assert isinstance(value, Operation)
        info = value.info
        if info is None:
            return # already materialized
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)
        # but only once
        value.info = None

    # optimize_alloc_removal unchanged


Version 5 Materialize Fields
===============================================

Now we need to solve a more difficult problem. So far, the virtual objects that
we have materialized have all been empty, meaning they didn't have any fields
written to at the point of materialization. Let's write a test for this:

.. code:: python

    def test_materialize_fields():
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.getarg(1)
        obj = bb.alloc()
        contents0 = bb.store(obj, 0, 8)
        contents1 = bb.store(obj, 1, var1)
        sto = bb.store(var0, 0, obj)

        # the virtual obj looks like this
        #  obj
        # ┌──────┬──────────┐
        # │ 0: 8 │ 1: var1  │
        # └──────┴──────────┘
        # then it needs to be materialized
        # this is the first example where a virtual
        # object that we want to materialize has any
        # content and is not just an empty object
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = getarg(1)
    optvar2 = alloc()
    optvar3 = store(optvar2, 0, 8)
    optvar4 = store(optvar2, 1, optvar1)
    optvar5 = store(optvar0, 0, optvar2)"""
        # fails so far! the operations we get atm
        # are:
        # optvar0 = getarg(0)
        # optvar1 = getarg(1)
        # optvar2 = alloc()
        # optvar3 = store(optvar0, 0, optvar2)
        # which is wrong, because the store operations
        # into optvar1 got lost

To fix this problem, we need to re-create a ``store`` operation for every
element of the the ``.contents`` dictionary of the virtual object we are
materializing. Let's do that in order of the field numbers by sorting the
dictionary's items:


.. code:: python
    :emphasize-lines: 11-14

    def materialize(opt_bb, value: Operation) -> None:
        if isinstance(value, Constant):
            return
        assert isinstance(value, Operation)
        info = value.info
        if info is None:
            return # already materialized
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)
        # put the content back
        for idx, val in sorted(info.contents.items()):
            # re-create store operation
            opt_bb.store(value, idx, val)
        # only materialize once
        value.info = None

    # optimize_alloc_removal unchanged

This is enough to pass the test.


Version 6 Recursive Materialization
======================================

Next problem: In the above example, the fields of the virtual objects contained
only constants or non-virtual objects. However, we could have a situation where
a whole tree of virtual objects is built, and then the root of the tree escapes.
This makes it necessary to escape the whole tree. Let's write a test for the
case of only two virtual objects though:


.. code:: python

    def test_materialize_chained_objects():
        bb = Block()
        var0 = bb.getarg(0)
        obj0 = bb.alloc()
        obj1 = bb.alloc()
        contents = bb.store(obj0, 0, obj1)
        const = bb.store(obj1, 0, 1337)
        sto = bb.store(var0, 0, obj0)
        #  obj0
        # ┌──────┐
        # │ 0: ╷ │
        # └────┼─┘
        #      │
        #      ▼
        #     obj1
        #   ┌─────────┐
        #   │ 0: 1337 │
        #   └─────────┘
        # now obj0 escapes
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = alloc()
    optvar3 = store(optvar2, 0, 1337)
    optvar4 = store(optvar1, 0, optvar2)
    optvar5 = store(optvar0, 0, optvar1)"""
        # fails in an annoying way! the resulting
        # basic block is not in proper SSA form
        # so printing doesn't work. The optimized
        # block would look like this:
        # optvar0 = getarg(0)
        # optvar1 = alloc()
        # optvar3 = store(optvar1, 0, optvar2)
        # optvar4 = store(optvar0, 0, optvar1)
        # where optvar2 is an ``alloc`` Operation
        # that is not itself in the output block

To fix it, ``materialize`` needs to call itself recursively for all the field
values of the virtual object:

.. code:: python
    :emphasize-lines: 13-14

    def materialize(opt_bb, value: Operation) -> None:
        if isinstance(value, Constant):
            return
        assert isinstance(value, Operation)
        info = value.info
        if info is None:
            return # already materialized
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)
        # put the content back
        for idx, val in sorted(info.contents.items()):
            # materialize recursively
            materialize(opt_bb, val)
            opt_bb.store(value, idx, val)
        # only materialize once
        value.info = None

    # optimize_alloc_removal unchanged

This is pretty great, the materialization logic is getting pretty good. We need
to fix a subtle problem next though.

Version 7 Dealing with Object Cycles
====================================

The bug in this section is a bit tricky, and does not immediately occur. In
fact, in PyPy a variant of it was hiding out in our optimizer for quite a while
until we found it much later (despite us being aware of the general problem and
correctly dealing with it in other cases).

The problem is this: a virtual object can (directly or indirectly) point to
itself, and we must carefully deal with that case to avoid infinite recursion in
``materialize``. Here's the simplest test:

.. code:: python

    def test_object_graph_cycles():
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.alloc()
        var2 = bb.store(var1, 0, var1)
        var3 = bb.store(var0, 1, var1)
        #   ┌────────┐
        #   ▼        │
        #  obj0      │
        # ┌──────┐   │
        # │ 0: ╷ │   │
        # └────┼─┘   │
        #      │     │
        #      └─────┘
        # obj0 points to itself, and then it is
        # escaped
        opt_bb = optimize_alloc_removal(bb)
        # the previous line fails with an
        # InfiniteRecursionError
        # materialize calls itself, from the line
        # materialize(opt_bb, val), infinitely

        # what we want is instead this output:
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = store(optvar1, 0, optvar1)
    optvar3 = store(optvar0, 1, optvar1)"""

The fix is not a big change, but a little bit subtle nevertheless. We change the
order in which things are done in ``materialize``. Right after emitting the
``alloc``, we set the ``.info`` to ``None``, to mark the object as not virtual.
Only afterwards do we re-create the stores and call ``materialize`` recursively.


.. code:: python
    :emphasize-lines: 11-17

    def materialize(opt_bb, value: Operation) -> None:
        if isinstance(value, Constant):
            return
        assert isinstance(value, Operation)
        info = value.info
        if info is None:
            return # already materialized
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)
        # only materialize once
        value.info = None
        # put the content back
        for idx, val in sorted(info.contents.items()):
            # materialize recursively
            materialize(opt_bb, val)
            opt_bb.store(value, idx, val)

Version 8 Loading from non-virtual objects
===========================================

Now materialize is done. We need to go back to ``optimize_alloc_removal`` and
improve it a bit. The last time we changed it, we added a case analysis to the
code dealing with ``store``, distinguishing between storing to a virtual and to
a non-virtual object. We need to add an equivalent distinction to the ``load``
case, because right now loading from a non-virtual crashes.

.. code:: python

    def test_load_non_virtual():
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.load(var0, 0)
        bb.escape(var1)
        # the next line fails in the line
        # op.make_equal_to(info.load(field))
        # because info is None
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = load(optvar0, 0)
    optvar2 = escape(optvar1)"""

To fix it, we split the ``load`` code into two cases, leaving the virtual path
as before, and letting the ``load`` from a non-virtual fall through to the
general code at the end of the function.

.. code:: python
    :emphasize-lines: 9-14

    def optimize_alloc_removal(bb):
        opt_bb = Block()
        for op in bb:
            if op.name == "alloc":
                op.info = VirtualObject()
                continue
            if op.name == "load":
                info = op.arg(0).info
                if info: # virtual
                    field = get_num(op)
                    op.make_equal_to(info.load(field))
                    continue
                # otherwise not virtual, use the
                # general path below
            if op.name == "store":
                info = op.arg(0).info
                if info: # virtual
                    field = get_num(op)
                    info.store(field, op.arg(2))
                    continue
                else: # not virtual
                    # first materialize the
                    # right hand side
                    materialize(opt_bb, op.arg(2))
                    # then emit the store via
                    # the general path below
            opt_bb.append(op)
        return opt_bb



Version 9 Final: Materialize on Other Operations
==================================================

We're almost at the end now. There's one final generalization left to do. We
started with the heuristic that storing a virtual into a non-virtual would
escape it. This should be generalized. Every time we pass a virtual into any
operation where it is not the first argument of a ``load`` and a ``store``
should also escape it (imagine passing the virtual to ``print`` or something
like that). Let's test this as usual with our general ``escape`` operation:


.. code:: python

    def test_materialize_on_other_ops():
        # materialize not just on store
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.alloc()
        var2 = bb.escape(var1)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = escape(optvar1)"""
        # again, the resulting basic block is not in
        # valid SSA form

To fix this, we will take the call to ``materialize`` out of the ``store`` code
path and instead put it into the generic code path the end of the ``while``
loop:

.. code:: python
    :emphasize-lines: 35-39

    # materialize is unchanged
    def materialize(opt_bb, value: Value) -> None:
        if isinstance(value, Constant):
            return
        assert isinstance(value, Operation)
        info = value.info
        if not info:
            # Already materialized
            return
        assert value.name == "alloc"
        opt_bb.append(value)
        value.info = None
        for idx, val in sorted(info.contents.items()):
            materialize(opt_bb, val)
            opt_bb.store(value, idx, val)

    def optimize_alloc_removal(bb):
        opt_bb = Block()
        for op in bb:
            if op.name == "alloc":
                op.info = VirtualObject()
                continue
            if op.name == "load":
                info = op.arg(0).info
                if info: # virtual
                    field = get_num(op)
                    op.make_equal_to(info.load(field))
                    continue
            if op.name == "store":
                info = op.arg(0).info
                if info: # virtual
                    field = get_num(op)
                    info.store(field, op.arg(2))
                    continue
            # materialize all the arguments of
            # operations that are put into the
            # output basic block
            for arg in op.args:
                materialize(opt_bb, arg.find())
            opt_bb.append(op)
        return opt_bb

That's it, we're done. It's not a lot of code, but actually quite a powerful
optimization.

.. code:: python

    def test_sink_allocations():
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.alloc()
        var2 = bb.store(var1, 0, 123)
        var3 = bb.store(var1, 1, 456)
        var4 = bb.load(var1, 0)
        var5 = bb.load(var1, 1)
        var6 = bb.add(var4, var5)
        var7 = bb.store(var1, 0, var6)
        var8 = bb.store(var0, 1, var1)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = add(123, 456)
    optvar2 = alloc()
    optvar3 = store(optvar2, 0, optvar1)
    optvar4 = store(optvar2, 1, 456)
    optvar5 = store(optvar0, 1, optvar2)"""
