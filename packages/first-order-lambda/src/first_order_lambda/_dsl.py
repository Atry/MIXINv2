"""A Higher-Order Abstract Syntax surface, compiled to the first-order de Bruijn AST.

Object-language binders are written with Python ``lambda``, so terms read isomorphically to
the lambda-calculus, and Python's lexical scope is the implicit symbol table (no name
environment, no capture handling). ``mu(lambda this: ...)`` is the single-point recursion
binder. The Python lambdas run once at build time; the result is a pure first-order tree
(``Lam``/``App``/``Var``/``Mu``), so interning and node identity are unaffected. Do not tie
knots with zero-argument ``lambda: x`` thunks, which would build a cyclic Python object
graph rather than a tree.
"""

from __future__ import annotations

from typing import Callable

from first_order_lambda._ast import Node, make_app, make_lam, make_mu, make_var

Builder = Callable[[int], Node]
"""A HOAS term: given the current binder depth, produce a de Bruijn node."""


def var_at(level: int) -> Builder:
    return lambda depth: make_var(depth - level - 1)


def lam(body: Callable[[Builder], Builder]) -> Builder:
    return lambda depth: make_lam(body(var_at(depth))(depth + 1))


def mu(body: Callable[[Builder], Builder]) -> Builder:
    return lambda depth: make_mu(body(var_at(depth))(depth + 1))


def app(function: Builder, argument: Builder) -> Builder:
    return lambda depth: make_app(function(depth), argument(depth))


def build(term: Builder) -> Node:
    """Finalize a HOAS term into a de Bruijn ``Node``."""
    return term(0)
