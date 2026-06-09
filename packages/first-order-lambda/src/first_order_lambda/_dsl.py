"""A Higher-Order Abstract Syntax surface, compiled to the first-order de Bruijn AST.

Object-language binders are written with Python ``lambda``, so terms read isomorphically to
the lambda-calculus, and Python's lexical scope is the implicit symbol table (no name
environment, no capture handling). The calculus is pure (``Var``/``Lam``/``App``); cyclic and
recursive data are written with the ``Y`` combinator (no recursion binder is needed, since
interning folds the structurally-repeating positions a ``Y`` recursion produces). The Python
lambdas run once at build time; the result is a pure first-order tree.
"""

from __future__ import annotations

import inspect

from typing import Callable

from first_order_lambda._ast import Node, make_app, make_lam, make_var

Builder = Callable[[int], Node]
"""A HOAS term: given the current binder depth, produce a de Bruijn node."""


def _by_depth(produce: Callable[[int], Node]) -> Builder:
    """Memoise a builder's node by binder depth.

    A builder is a pure function of the binder depth, so reusing the same builder object in several
    places (a shared subterm) yields the same node at a given depth. Caching by depth makes a
    shared-builder DAG build in time linear in its distinct nodes instead of unfolding it into a
    tree: ``build`` invokes each child builder per occurrence, so without this a builder reused in
    ``n`` places is re-run ``n`` times. The result nodes are interned regardless; this shares the
    construction work too.
    """
    cache: dict[int, Node] = {}

    def at(depth: int) -> Node:
        node = cache.get(depth)
        if node is None:
            node = produce(depth)
            cache[depth] = node
        return node

    return at


def var_at(level: int) -> Builder:
    return _by_depth(lambda depth: make_var(depth - level - 1))


def lam(body: Callable[[Builder], Builder]) -> Builder:
    return _by_depth(lambda depth: make_lam(body(var_at(depth))(depth + 1)))


def app(function: Builder, argument: Builder) -> Builder:
    return _by_depth(lambda depth: make_app(function(depth), argument(depth)))


def curry(body: "Callable[..., Builder]") -> Builder:
    """Expand an N-argument Python function into a curried HOAS lambda.

    ``curry(lambda a, b, c: e)`` is ``lam(lambda a: lam(lambda b: lam(lambda c: e)))``: the
    function's parameter count (read with ``inspect``) fixes the binder arity, and each parameter
    is the ``Builder`` for a bound variable. A zero-argument ``body`` builds no binder and returns
    ``body()`` directly. This is sugar for the nested ``lam`` chains that multi-argument terms need.
    """
    arity = len(inspect.signature(body).parameters)

    def collect(arguments: "list[Builder]") -> Builder:
        if len(arguments) == arity:
            return body(*arguments)
        return lam(lambda bound: collect([*arguments, bound]))

    return collect([])


def build(term: Builder) -> Node:
    """Finalize a HOAS term into a de Bruijn ``Node``."""
    return term(0)
