.. title: Allocation Removal in the Toy Optimizer
.. slug: toy-optimizer-allocation-removal
.. date: 2022-07-30 15:00:00 UTC
.. tags:
.. category:
.. link:
.. description:
.. type: rest
.. author: Carl Friedrich Bolz-Tereick

Previous code:

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


Interpreter
=============

new operation ``alloc``, ``store``, ``load``

write an interpreter so that we know what they do.

.. code:: python

    def test_interpret():
        bb = Block()
        var0 = bb.getarg(0)
        ls = bb.alloc()
        sto = bb.store(ls, 0, var0)
        var1 = bb.load(ls, 0)
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
        results : dict[Operation, Any] = {}
        def argval(op, i):
            arg = op.arg(i)
            if isinstance(arg, Constant):
                return arg.value
            else:
                assert isinstance(arg, Operation)
                return results[arg]

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
            results[op] = res


Version 1: Naive Attempt
========================

motivation short lived objects. first naive version

.. code:: python

    class VirtualObject:
        def __init__(self):
            self.contents: dict[int, Value] = {}

        def store(self, idx, value):
            self.contents[idx] = value

        def load(self, idx):
            return self.contents[idx]


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

    def test_remove_unused_allocation():
        # the virtual object looks like this:
        #  ls
        # ┌──────────┐
        # │ 0: var0  │
        # └──────────┘
        bb = Block()
        var0 = bb.getarg(0)
        ls = bb.alloc()
        sto = bb.store(ls, 0, var0)
        var1 = bb.load(ls, 0)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)"""



Version 2: Re-Materialize Allocations
======================================

.. code:: python

    def test_rematerialize():
        #  ls virtual
        # ┌───────┐
        # │ empty │
        # └───────┘
        # and then we store into field 0 of var0 a
        # reference to ls. since var0 is not virtual,
        # ls must escape, so we have to put it back
        # into the optimized basic block
        bb = Block()
        var0 = bb.getarg(0)
        ls = bb.alloc()
        sto = bb.store(var0, 0, ls)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = store(optvar0, 0, optvar1)"""
        # so far, fails like this:
        # the line:
        # info.store(field, op.arg(2))
        # produces an AttributeError because info
        # is None

.. code:: python
    :emphasize-lines: 1-8,23-28

    def materialize(opt_bb, value: Operation) -> None:
        assert not isinstance(value, Constant)
        assert isinstance(value, Operation)
        info = value.info
        assert info
        assert value.name == "alloc"
        # put the alloc operation back into the trace
        opt_bb.append(value)

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
                if info:
                    field = get_num(op)
                    info.store(field, op.arg(2))
                    continue
                else:
                    materialize(opt_bb, op.arg(2))
            opt_bb.append(op)
        return opt_bb


Version 3: Don't Materialize Twice
===================================


.. code:: python

    def test_dont_materialize_twice():
        # ls is again an empty virtual object, and we
        # store it into var0 *twice*. this should
        # only materialize it once, though!
        bb = Block()
        var0 = bb.getarg(0)
        ls = bb.alloc()
        sto0 = bb.store(var0, 0, ls)
        sto1 = bb.store(var0, 0, ls)
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

.. code:: python

    def test_materialize_fields():
        # the virtual ls looks like this
        #  ls
        # ┌──────┬──────┐
        # │ 0: 7 │ 1: 8 │
        # └──────┴──────┘
        # then it needs to be materialized
        # this is the first example where virtual
        # object that we want to materialize has any
        # content and is not just an empty object
        bb = Block()
        var0 = bb.getarg(0)
        ls = bb.alloc()
        contents0 = bb.store(ls, 1, 8)
        contents1 = bb.store(ls, 0, 7)
        sto = bb.store(var0, 0, ls)
        opt_bb = optimize_alloc_removal(bb)
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = store(optvar1, 0, 7)
    optvar3 = store(optvar1, 1, 8)
    optvar4 = store(optvar0, 0, optvar1)"""
        # fails so far! the operations we get atm
        # are:
        # optvar0 = getarg(0)
        # optvar1 = alloc()
        # optvar2 = store(optvar0, 0, optvar1)


.. code:: python
    :emphasize-lines: 11-13

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
            opt_bb.store(value, idx, val)
        # only materialize once
        value.info = None

    # optimize_alloc_removal unchanged

Version 6 Recursive Materialization
======================================


.. code:: python

    def test_materialize_chained_objects():
        #  ls0
        # ┌──────┐
        # │ 0: ╷ │
        # └────┼─┘
        #      │
        #      ▼
        #     ls1
        #   ┌─────────┐
        #   │ 0: 1337 │
        #   └─────────┘
        # now ls0 escapes
        bb = Block()
        var0 = bb.getarg(0)
        ls0 = bb.alloc()
        ls1 = bb.alloc()
        contents = bb.store(ls0, 0, ls1)
        const = bb.store(ls1, 0, 1337)
        sto = bb.store(var0, 0, ls0)
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
        # so printing doesn't work


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

Version 7 Dealing with Object Cycles
====================================

.. code:: python

    def test_object_graph_cycles():
        #   ┌────────┐
        #   ▼        │
        #  ls0       │
        # ┌──────┐   │
        # │ 0: ╷ │   │
        # └────┼─┘   │
        #      │     │
        #      └─────┘
        # ls0 points to itself, and then it is
        # escaped
        bb = Block()
        var0 = bb.getarg(0)
        var1 = bb.alloc()
        var2 = bb.store(var1, 0, var1)
        var3 = bb.store(var0, 1, var1)
        opt_bb = optimize_alloc_removal(bb)
        # the previous line fails with an
        # InfiniteRecursionError
        # materialize calls itself, from the line
        # materialize(opt_bb, val), infinitely
        assert bb_to_str(opt_bb, "optvar") == """\
    optvar0 = getarg(0)
    optvar1 = alloc()
    optvar2 = store(optvar1, 0, optvar1)
    optvar3 = store(optvar0, 1, optvar1)"""




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

Version 8, Final: Materialize on Other Operations
==================================================


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


.. code:: python
    :emphasize-lines: 35-36

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
                if info:
                    field = get_num(op)
                    op.make_equal_to(info.load(field))
                    continue
            if op.name == "store":
                info = op.arg(0).info
                if info:
                    field = get_num(op)
                    info.store(field, op.arg(2))
                    continue
            for arg in op.args:
                materialize(opt_bb, arg.find())
            opt_bb.append(op)
        return opt_bb

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
