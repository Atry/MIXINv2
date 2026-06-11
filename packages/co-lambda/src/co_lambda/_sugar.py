"""Shared HOAS transcription sugar: fixed-shape notation for writing lambda terms.

This module is one of the four strictly separated kinds (codec / sugar / runtime / pure-lambda
compiler source). Everything here is a one-to-one notational transcription: parameters are Builders
(or Python callables standing for object-language binders), the produced shape is literal at the
call site, and nothing is computed from data. The pure-lambda source modules import their writing
notation from here (and from ``_dsl``/``_pybuild``), so no Python helper definitions live next to
the lambda terms themselves.
"""

from __future__ import annotations

from co_lambda._dsl import Builder, app, lam
from co_lambda._prelude import FALSE, MAP, SCOTT_CONS, SCOTT_NIL, TRUE


def ap(function: Builder, *arguments: Builder) -> Builder:
    """Left-folded application: ``ap(f, x, y, z)`` is ``((f x) y) z``."""
    result = function
    for argument in arguments:
        result = app(result, argument)
    return result


def let(value: Builder, body) -> Builder:
    """Bind ``value`` for ``body`` (a Python ``lambda`` over the bound Builder)."""
    return app(lam(body), value)


def split_pair(pair_value: Builder, body) -> Builder:
    """Destructure a continuation pair (``pair k = k first second``) for ``body`` (a Python
    ``lambda`` over the two bound Builders)."""
    return app(pair_value, lam(lambda first: lam(lambda second: body(first, second))))


def pair(first: Builder, second: Builder) -> Builder:
    """The continuation pair: ``lambda k. k first second``."""
    return lam(lambda consume: ap(consume, first, second))


def split_triple(triple_value: Builder, body) -> Builder:
    """Destructure a right-nested triple ``pair(a, pair(b, c))`` for ``body(a, b, c)``."""
    return split_pair(triple_value, lambda first, rest: split_pair(
        rest, lambda second, third: body(first, second, third),
    ))


def split_quad(quad_value: Builder, body) -> Builder:
    """Destructure a right-nested quadruple ``pair(a, pair(b, pair(c, d)))`` for ``body(a, b, c, d)``."""
    return split_pair(quad_value, lambda first, rest: split_triple(
        rest, lambda second, third, fourth: body(first, second, third, fourth),
    ))


def pair_first(pair_value: Builder) -> Builder:
    return app(pair_value, TRUE)


def pair_second(pair_value: Builder) -> Builder:
    return app(pair_value, FALSE)


def cons(head: Builder, tail: Builder) -> Builder:
    return ap(SCOTT_CONS, head, tail)


def one(element: Builder) -> Builder:
    return cons(element, SCOTT_NIL)


def two(first: Builder, second: Builder) -> Builder:
    return cons(first, cons(second, SCOTT_NIL))


def map_list(function: Builder, source: Builder) -> Builder:
    return ap(MAP, function, source)
