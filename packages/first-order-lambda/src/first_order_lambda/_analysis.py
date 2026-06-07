"""Specialization analysis written in the lambda-calculus itself.

The analysis that decides which sub-terms to specialize is a pure lambda term, run by the
interpreter on the quoted program, so the calculus analyzes its own programs: a demonstration that
tabling-based reduction expresses program analysis, not only evaluation. This module holds the
first and simplest certificate, a closedness check, which is exactly the precondition a compiled
island needs (a closed sub-term can be compiled and embedded; an open one depends on its context).
Richer certificates (folding-based rationality, typability) layer on later in the same style.

``CLOSED`` consumes a quoted term (the Scott value ``QVar i`` / ``QLam b`` / ``QApp f a`` produced by
``quote``) and returns a Church boolean. It recurses structurally with the strict fixpoint ``Z``,
threading a Church-numeral binder depth: a variable is in scope when its index is below the depth,
an abstraction recurses at ``depth + 1``, and an application is closed when both sides are. The
arithmetic (``<``, ``and``) is the usual Church encoding, so the whole analysis stays inside the pure
calculus.
"""

from __future__ import annotations

from first_order_lambda._ast import Node, make_app, make_var
from first_order_lambda._compiler import Z, quote
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import FALSE, IS_ZERO, PRED, SUCC, church
from first_order_lambda._shape import VarShape

# Church arithmetic for the closedness check (truncated subtraction gives the comparisons).
_SUBTRACT: Builder = lam(lambda a: lam(lambda b: app(app(b, PRED), a)))  # a - b, floored at zero
_AT_MOST: Builder = lam(lambda a: lam(lambda b: app(IS_ZERO, app(app(_SUBTRACT, a), b))))  # a <= b
_LESS_THAN: Builder = lam(lambda a: lam(lambda b: app(app(_AT_MOST, app(SUCC, a)), b)))  # a < b
_AND: Builder = lam(lambda p: lam(lambda q: app(app(p, q), FALSE)))

# CLOSED = Z (lambda self. lambda depth. lambda quoted.
#   quoted (lambda index. index < depth)                       -- QVar index
#          (lambda body. self (succ depth) body)               -- QLam body
#          (lambda f. lambda a. and (self depth f) (self depth a)))  -- QApp f a
CLOSED: Builder = app(
    Z,
    lam(lambda self_recursion: lam(lambda depth: lam(lambda quoted: app(app(app(
        quoted,
        lam(lambda index: app(app(_LESS_THAN, index), depth)),
        ),
        lam(lambda body: app(app(self_recursion, app(SUCC, depth)), body)),
        ),
        lam(lambda function: lam(lambda argument: app(
            app(_AND, app(app(self_recursion, depth), function)),
            app(app(self_recursion, depth), argument),
        ))),
    )))),
)

_TRUE_MARKER = 7_100_001
_FALSE_MARKER = 7_100_002


def _interpret_boolean(node: Node) -> bool:
    """Observe a Church boolean by selecting between two distinct free-variable markers."""
    applied = make_app(make_app(node, make_var(_TRUE_MARKER)), make_var(_FALSE_MARKER))
    shape = applied.weak_head_normal_form
    match shape:
        case VarShape(index=index) if index == _TRUE_MARKER:
            return True
        case VarShape(index=index) if index == _FALSE_MARKER:
            return False
        case _:
            raise ValueError(f"not a Church boolean: {shape!r}")


def is_closed(node: Node) -> bool:
    """Whether ``node`` is closed, decided by running the lambda-level ``CLOSED`` analysis on it.

    The verdict is computed by the interpreter from the quoted program, so the certificate that
    drives island selection is itself a lambda term, not Python code.
    """
    verdict = build(app(app(CLOSED, church(0)), quote(node)))
    return _interpret_boolean(verdict)
