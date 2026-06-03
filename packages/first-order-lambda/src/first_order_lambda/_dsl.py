"""A Higher-Order Abstract Syntax surface, compiled to the first-order de Bruijn AST.

Object-language binders are written with Python ``lambda``, so terms read isomorphically to
the lambda-calculus, and Python's lexical scope is the implicit symbol table (no name
environment, no capture handling). The calculus is pure (``Var``/``Lam``/``App``); cyclic and
recursive data are written with the ``Y`` combinator (no recursion binder is needed, since
interning folds the structurally-repeating positions a ``Y`` recursion produces). The Python
lambdas run once at build time; the result is a pure first-order tree.
"""

from __future__ import annotations

from typing import Callable

from first_order_lambda._ast import Node, make_app, make_lam, make_var

Builder = Callable[[int], Node]
"""A HOAS term: given the current binder depth, produce a de Bruijn node."""


def var_at(level: int) -> Builder:
    return lambda depth: make_var(depth - level - 1)


def lam(body: Callable[[Builder], Builder]) -> Builder:
    return lambda depth: make_lam(body(var_at(depth))(depth + 1))


def app(function: Builder, argument: Builder) -> Builder:
    return lambda depth: make_app(function(depth), argument(depth))


def build(term: Builder) -> Node:
    """Finalize a HOAS term into a de Bruijn ``Node``."""
    return term(0)
