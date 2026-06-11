"""Imperative specialization of a productive rational stream: loops from folding.

``GEN`` is a pure lambda term that maps a Scott stream ``cons h t`` to a quoted output stream
``Yield h (GEN t)`` (and ``nil`` to ``Stop``). It is an ordinary productive recursion with nothing
loop-aware in it. Run on a *cyclic* source (e.g. ``Y (cons 0)``), the recursive ``GEN t`` re-enters
the same interned state, so the interpreter (``fixpoint_cached_property`` + interning) folds the back
edge and the output is a *cyclic* quoted stream. The cycle-aware decoder (``_examples``) walks that
output with a visited set and emits a Python generator whose ``while`` loop is exactly the folded back
edge. On a finite source the same ``GEN`` yields a finite, loopless generator.

This is not meta-tracing. Meta-tracing compiles traces *of an interpreter*, which requires the
interpreter to be written in the traced language (a self-interpreter); here the lambda term ``GEN``
is the program, and the interpreter folds *its* behaviour, so this is ahead-of-time specialization
of a program, not a trace of an interpreter.

This module is pure lambda calculus: every top-level binding is a ``Builder``. The output-stream
decoder and the demo driver live in ``_examples``.
"""

from __future__ import annotations

from co_lambda._dsl import Builder, app, lam
from co_lambda._prelude import Y

# Output stream: two literal Scott constructors (Yield value rest / Stop).
_S_STOP: Builder = lam(lambda on_yield: lam(lambda on_stop: on_stop))

# GEN = Y (lambda self. lambda s. s (lambda h. lambda t. Yield h (self t)) Stop)
GEN: Builder = app(
    Y,
    lam(lambda self_recursion: lam(lambda source: app(
        app(
            source,
            lam(lambda head: lam(lambda tail: lam(lambda on_yield: lam(lambda on_stop: app(
                app(on_yield, head), app(self_recursion, tail),
            ))))),
        ),
        _S_STOP,
    ))),
)
