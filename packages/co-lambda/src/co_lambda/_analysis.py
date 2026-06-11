"""Specialization analysis written in the lambda-calculus itself.

The analysis that decides which sub-terms to specialize is a pure lambda term, run by the
interpreter on the quoted program, so the calculus analyzes its own programs: a demonstration that
tabling-based reduction expresses program analysis, not only evaluation. This module holds the
closedness and depth measures; richer certificates (typability, fuel-bounded normalization) live in
``_typecheck`` and ``_reduce`` in the same style.

This module is pure lambda calculus: every top-level binding is a ``Builder`` (a ``@curry``-decorated
``def`` IS a Builder). The Python-side verdict readers live at the boundary (``_specialize``).

``LOOSE_BOUND`` is a DEPTH-FREE closedness measure, so the interpreter's interning shares it across
every position: ``LOOSE_BOUND quoted`` takes no binder depth, so ``app(LOOSE_BOUND, sub)`` is the
SAME node for an interned sub-term and is tabled once; a whole-tree scan is then linear. It returns
the number of enclosing binders the sub-term needs (the de Bruijn ``loose_bound``): a variable needs
index+1, an abstraction discharges one (floored at zero by ``PRED``), an application needs the larger
of the two. A sub-term is closed exactly when it needs none (``IS_CLOSED``).
"""

from __future__ import annotations

from co_lambda._dsl import Builder, app, curry, lam
from co_lambda._prelude import IS_ZERO, PRED, SUCC, Y
from co_lambda._sugar import ap

# Church arithmetic for the measures (truncated subtraction gives the comparisons).
_SUBTRACT: Builder = lam(lambda a: lam(lambda b: app(app(b, PRED), a)))  # a - b, floored at zero
_AT_MOST: Builder = lam(lambda a: lam(lambda b: app(IS_ZERO, ap(_SUBTRACT, a, b))))  # a <= b
_MAX: Builder = lam(lambda a: lam(lambda b: ap(_AT_MOST, a, b, b, a)))  # a <= b ? b : a

LOOSE_BOUND: Builder = app(Y, lam(lambda self_recursion: lam(lambda quoted: ap(
    quoted,
    lam(lambda index: app(SUCC, index)),  # QVar index: needs index+1 enclosing binders
    lam(lambda body: app(PRED, app(self_recursion, body))),  # QLam body: discharges one binder
    lam(lambda function: lam(lambda argument: ap(
        _MAX, app(self_recursion, function), app(self_recursion, argument),
    ))),  # QApp f a: the larger of the two
))))

IS_CLOSED: Builder = lam(lambda quoted: app(IS_ZERO, app(LOOSE_BOUND, quoted)))  # closed iff needs none


# DEPTH: the nesting depth of a quoted term (a Church numeral), a cheap path-free measure the interner
# shares per distinct sub-term. It bounds the simple-typability check: running algorithm-W on a large
# (deep) closed combinator is expensive and the no-GC interner retains every reduction, so a specializer
# only certifies an island when the sub-term is shallow enough (``depth_at_most``), leaving a deep closed
# region reconstructed as an interpreted graph rather than flattened to a strict island. The bound only
# ever makes the certificate MORE conservative (fewer islands), never unsound.
DEPTH: Builder = app(Y, lam(lambda self_recursion: lam(lambda quoted: ap(
    quoted,
    lam(lambda index: lam(lambda s: lam(lambda z: z))),  # QVar: a leaf (depth zero)
    lam(lambda body: app(SUCC, app(self_recursion, body))),  # QLam: one deeper
    lam(lambda function: lam(lambda argument: app(SUCC, ap(
        _MAX, app(self_recursion, function), app(self_recursion, argument),
    )))),  # QApp: one past the deeper side
))))


@curry
def depth_at_most(bound: Builder, quoted: Builder) -> Builder:
    """``DEPTH quoted <= bound`` (a Church boolean): the shallow-enough certificate."""
    return ap(_AT_MOST, app(DEPTH, quoted), bound)
