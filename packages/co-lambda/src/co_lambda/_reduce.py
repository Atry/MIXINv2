"""The fold oracle as a lambda term: does a quoted term have a finite normal form?

``CHOOSE_RUNTIME`` needs to know whether a term normalizes to a finite normal form (so call-by-need,
which never folds, reaches the same value) or only the interpreter's fold handles it (a cyclic, rational
behaviour). The Python ``_specialize.needs_folding`` reads this out of the interpreter with bounds; this
module is the pure-lambda port and the verdict that actually drives specialization.

It is a fuel-bounded normalizer written in the calculus. ``EVAL`` denotes a quoted de Bruijn term as a
value in a three-constructor semantic domain: ``VLAM`` (a fuel-aware host function), ``VNEU`` (a neutral:
a variable applied to value arguments), and ``VBOTTOM`` (the fuel ran out). Argument evaluation is lazy
because the interpreter running ``EVAL`` is itself call-by-name, so a normalizing term whose strict
reduction would diverge (``factorial`` through ``Y``) still reaches its normal form. A **BinNat fuel**
threads through every evaluation and walk step and decreases at each one, so a genuinely diverging head
reduction (``Omega``) hits ``VBOTTOM`` rather than looping. ``WALK`` forces the value to full normal form,
going under binders (applying a ``VLAM`` to a fresh neutral) and down neutral spines, threading the fuel
as a SINGLE sequential budget (the argument is walked with whatever fuel the head left), so total work is
linear in the fuel rather than exponential. ``NORMALIZES`` is whether the walk completes before the fuel
runs out: completion means a finite normal form was positively observed (call-by-need safe); exhaustion
is read conservatively as needs-fold (interpret), which is always sound. This mirrors ``needs_folding``.

This module is pure lambda calculus: every top-level binding is a ``Builder``. The verdict reader
(``normalizes_lambda``) and the fuel policy live at the boundary (``_specialize``); the large-stack
host machinery lives in ``_runtime``.
"""

from __future__ import annotations

from co_lambda._binnat import BIN_IS_ZERO, BIN_PRED, BIN_SUCC, BIN_ZERO
from co_lambda._dsl import Builder, app, lam
from co_lambda._prelude import FALSE, IS_ZERO, PRED, TRUE, Y
from co_lambda._sugar import ap

# Option: SOME remaining-fuel | NONE (exhausted); consumed as ``option some_handler none_value``.
_SOME: Builder = lam(lambda value: lam(lambda some_handler: lam(lambda none_value: app(some_handler, value))))
_NONE: Builder = lam(lambda some_handler: lam(lambda none_value: none_value))


# --- environment as a Scott list ----------------------------------------------------------------
_NIL: Builder = lam(lambda nil_value: lam(lambda cons_handler: nil_value))
_CONS: Builder = lam(lambda head: lam(lambda tail: lam(lambda nil_value: lam(lambda cons_handler: ap(cons_handler, head, tail)))))


# --- the semantic domain: VLAM function | VNEU neutral | VBOTTOM (consumed with three handlers) ---
# A neutral is NVAR level | NAPP neutral value.
_VLAM: Builder = lam(lambda function: lam(lambda on_lam: lam(lambda on_neu: lam(lambda on_bottom: app(on_lam, function)))))
_VNEU: Builder = lam(lambda neutral: lam(lambda on_lam: lam(lambda on_neu: lam(lambda on_bottom: app(on_neu, neutral)))))
_VBOTTOM: Builder = lam(lambda on_lam: lam(lambda on_neu: lam(lambda on_bottom: on_bottom)))

_NVAR: Builder = lam(lambda level: lam(lambda on_var: lam(lambda on_app: app(on_var, level))))
_NAPP: Builder = lam(lambda neutral: lam(lambda argument: lam(lambda on_var: lam(lambda on_app: ap(on_app, neutral, argument)))))


# nth env index: the index-th environment value (de Bruijn lookup); a free variable (empty environment)
# reads as a neutral, so an open term is handled and a closed one never reaches it. The index is a
# CHURCH numeral (quote emits ``q_var(church(i))``), so it is compared with Church ``IS_ZERO``/``PRED``;
# only the fuel and the binder level are BinNats.
_NTH: Builder = app(Y, lam(lambda nth: lam(lambda env: lam(lambda index: ap(
    env,
    app(_VNEU, app(_NVAR, index)),
    lam(lambda head: lam(lambda tail: ap(
        app(IS_ZERO, index),
        head,
        ap(nth, tail, app(PRED, index)),
    ))),
)))))


# apply fuel value argument: semantic application. A VLAM fires (passing the fuel on to its body
# evaluation); a VNEU grows its spine; VBOTTOM stays bottom.
_APPLY: Builder = lam(lambda fuel: lam(lambda value: lam(lambda argument: ap(
    value,
    lam(lambda function: ap(function, fuel, argument)),  # VLAM: invoke the fuel-aware closure
    lam(lambda neutral: app(_VNEU, ap(_NAPP, neutral, argument))),  # VNEU: extend the spine
    _VBOTTOM,  # VBOTTOM: absorbing
))))


# eval fuel env quoted: denote the quoted de Bruijn term as a value, threading the fuel.
# Argument evaluation (the second eval in the QApp case) is left lazy by the call-by-name interpreter,
# so a normalizing term whose strict reduction would diverge still reaches its value.
_EVAL: Builder = app(Y, lam(lambda eval_recursion: lam(lambda fuel: lam(lambda env: lam(lambda quoted: ap(
    BIN_IS_ZERO, fuel,
    _VBOTTOM,
    ap(
        quoted,
        lam(lambda index: ap(_NTH, env, index)),  # QVar: look up the value
        lam(lambda body: app(_VLAM, lam(lambda inner_fuel: lam(lambda argument: ap(
            eval_recursion, inner_fuel, ap(_CONS, argument, env), body,
        ))))),  # QLam: a fuel-aware closure
        lam(lambda function: lam(lambda argument: ap(
            _APPLY,
            app(BIN_PRED, fuel),
            ap(eval_recursion, app(BIN_PRED, fuel), env, function),
            ap(eval_recursion, app(BIN_PRED, fuel), env, argument),
        ))),  # QApp: apply (the argument value stays lazy)
    ),
))))))


# walk_neutral walk fuel level neutral: force a neutral's spine, threading the fuel as a single budget
# (the argument is walked with whatever fuel the head left), so total work is linear in the fuel rather
# than exponential. Returns SOME remaining-fuel on completion or NONE on exhaustion.
_WALK_NEUTRAL: Builder = app(Y, lam(lambda walk_neutral: lam(lambda walk: lam(lambda fuel: lam(lambda level: lam(lambda neutral: ap(
    BIN_IS_ZERO, fuel,
    _NONE,
    ap(
        neutral,
        lam(lambda variable_level: app(_SOME, app(BIN_PRED, fuel))),  # NVAR: a leaf, the spine ends
        lam(lambda inner_neutral: lam(lambda argument: ap(
            ap(walk_neutral, walk, app(BIN_PRED, fuel), level, inner_neutral),
            lam(lambda fuel_left: ap(walk, fuel_left, level, argument)),  # head done: walk the argument
            _NONE,  # head exhausted: propagate
        ))),
    ),
)))))))


# walk fuel level value: force the value to its full normal form, threading the fuel as a single budget;
# returns SOME remaining-fuel on completion or NONE on exhaustion. Going under a VLAM applies it to a
# fresh neutral (NVAR level) and recurses at level+1; a VNEU walks its spine; VBOTTOM (the evaluator ran
# out) is not a normal form.
_WALK: Builder = app(Y, lam(lambda walk: lam(lambda fuel: lam(lambda level: lam(lambda value: ap(
    BIN_IS_ZERO, fuel,
    _NONE,
    ap(
        value,
        lam(lambda function: ap(
            walk,
            app(BIN_PRED, fuel),
            app(BIN_SUCC, level),
            ap(function, app(BIN_PRED, fuel), app(_VNEU, app(_NVAR, level))),
        )),
        lam(lambda neutral: ap(_WALK_NEUTRAL, walk, app(BIN_PRED, fuel), level, neutral)),
        _NONE,  # VBOTTOM
    ),
))))))


# normalizes fuel quoted: whether walking the value of the quoted term to normal form completes within
# the fuel. SOME (completed) -> True (a finite normal form); NONE (exhausted) -> False (needs-fold).
NORMALIZES: Builder = lam(lambda fuel: lam(lambda quoted: ap(
    ap(_WALK, fuel, BIN_ZERO, ap(_EVAL, fuel, _NIL, quoted)),
    lam(lambda fuel_left: TRUE),
    FALSE,
)))
