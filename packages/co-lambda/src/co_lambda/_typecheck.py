"""Simple-typability as a lambda term: algorithm-W (STLC) written in the pure calculus.

This is the soundness certificate the specializer needs. ``TYPABLE`` consumes a quoted term (the
``QVar``/``QLam``/``QApp`` Scott value ``quote`` produces) and returns a Church boolean: whether the
term is simply typable, which is a sound certificate of strong normalization (so the strict
call-by-value runtime is safe). The Python ``_specialize._Inference`` is the specification this
ports and the test oracle it is checked against; it is not on the compile path.

This module is pure lambda calculus: every top-level binding is a ``Builder`` (a ``@curry``-decorated
``def`` IS a Builder). The Python-side verdict readers (``is_typable_lambda``, ``typable_bu_lambda``)
live at the boundary (``_specialize``).

The encoding is monomorphic algorithm-W (one fresh monotype per binder, no generalization), threading
a state of ``(next-fresh-id, substitution, failed-flag)`` purely:

* Types are a two-constructor Scott value: ``TVAR id`` (``id`` a BinNat, so allocating and comparing
  type variables is O(log id)) and ``TARROW l r``.
* The substitution is a function ``id -> Option Type`` (the empty map is ``lambda id. NONE``; extension
  shadows by id-equality), so ``resolve`` follows the chain and ``occurs`` walks the resolved type.
* ``unify`` threads ``(substitution, failed)`` and sets ``failed`` when the occurs check fires, which is
  exactly why the self-application ``x x`` (constraint ``alpha = alpha -> beta``) is untypable.
* ``infer`` threads the whole state and returns ``(state, type)``; a binder extends the typing context
  (a Scott list indexed by de Bruijn index) with a fresh monotype. It short-circuits once failed, so an
  untypable term is rejected as soon as the first occurs check fires.

Termination: ``infer`` recurses structurally on the term; the occurs check keeps the substitution
acyclic, so ``resolve``/``occurs``/``unify`` recurse on finite type trees. The verdict is therefore a
normal-form Church boolean.
"""

from __future__ import annotations

from co_lambda._binnat import BIN_ADD, BIN_EQUAL, BIN_SUCC, BIN_ZERO
from co_lambda._dsl import Builder, app, lam
from co_lambda._prelude import FALSE, IS_ZERO, OR, PRED, TRUE, Y
from co_lambda._sugar import ap, let, pair, split_pair, split_quad, split_triple

# --- booleans -------------------------------------------------------------------------------------
_NOT: Builder = lam(lambda boolean: ap(boolean, FALSE, TRUE))

# Option: SOME carries a value, NONE is empty; consumed as ``option some_handler none_value``.
_SOME: Builder = lam(lambda value: lam(lambda some_handler: lam(lambda none_value: app(some_handler, value))))
_NONE: Builder = lam(lambda some_handler: lam(lambda none_value: none_value))

# Scott list: consumed as ``list nil_value cons_handler``.
_NIL: Builder = lam(lambda nil_value: lam(lambda cons_handler: nil_value))
_CONS: Builder = lam(lambda head: lam(lambda tail: lam(lambda nil_value: lam(lambda cons_handler: ap(cons_handler, head, tail)))))

# --- types: TVAR id | TARROW left right (consumed as ``type var_handler arrow_handler``) ----------
_TVAR: Builder = lam(lambda identifier: lam(lambda var_handler: lam(lambda arrow_handler: app(var_handler, identifier))))
_TARROW: Builder = lam(lambda left: lam(lambda right: lam(lambda var_handler: lam(lambda arrow_handler: ap(arrow_handler, left, right)))))

# --- substitution: a function id -> Option Type --------------------------------------------------
_EMPTY_SUBST: Builder = lam(lambda identifier: _NONE)
# extend subst id type = a new map shadowing ``id`` with ``SOME type``.
_EXTEND: Builder = lam(lambda subst: lam(lambda identifier: lam(lambda bound: lam(lambda lookup: ap(
    ap(BIN_EQUAL, lookup, identifier),
    app(_SOME, bound),
    app(subst, lookup),
)))))

# resolve subst type: follow the substitution chain to the representative type.
_RESOLVE: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda type_: ap(
    type_,
    lam(lambda identifier: ap(
        app(subst, identifier),
        lam(lambda found: ap(self_recursion, subst, found)),
        app(_TVAR, identifier),
    )),
    lam(lambda left: lam(lambda right: ap(_TARROW, left, right))),
)))))

# occurs subst id type: whether ``id`` occurs in the resolved ``type`` (the occurs check).
_OCCURS: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda identifier: lam(lambda type_: let(
    ap(_RESOLVE, subst, type_),
    lambda resolved: ap(
        resolved,
        lam(lambda other: ap(BIN_EQUAL, other, identifier)),
        lam(lambda left: lam(lambda right: ap(
            OR,
            ap(self_recursion, subst, identifier, left),
            ap(self_recursion, subst, identifier, right),
        ))),
    ),
))))))

# bind subst id type: if the occurs check fires, fail; else extend the substitution. The result is a
# pair (substitution, failed).
_BIND: Builder = lam(lambda subst: lam(lambda identifier: lam(lambda bound: ap(
    ap(_OCCURS, subst, identifier, bound),
    pair(subst, TRUE),
    pair(ap(_EXTEND, subst, identifier, bound), FALSE),
))))

# unify state a b, with state = (substitution, failed): unify the two types, threading the state.
# Short-circuits when already failed; otherwise resolves both sides and matches the four shape cases:
# var/var (equal: nothing; else bind), var/arrow and arrow/var (bind after occurs check), arrow/arrow
# (unify the components left to right).
_UNIFY: Builder = app(Y, lam(lambda self_recursion: lam(lambda state: lam(lambda left_type: lam(lambda right_type: split_pair(
    state,
    lambda subst, failed: ap(
        failed,
        state,
        let(ap(_RESOLVE, subst, left_type), lambda left: let(ap(_RESOLVE, subst, right_type), lambda right: ap(
            left,
            lam(lambda left_id: ap(
                right,
                lam(lambda right_id: ap(ap(BIN_EQUAL, left_id, right_id), state, ap(_BIND, subst, left_id, right))),
                lam(lambda right_left: lam(lambda right_right: ap(_BIND, subst, left_id, right))),
            )),
            lam(lambda left_left: lam(lambda left_right: ap(
                right,
                lam(lambda right_id: ap(_BIND, subst, right_id, left)),
                lam(lambda right_left: lam(lambda right_right: ap(
                    self_recursion,
                    ap(self_recursion, state, left_left, right_left),
                    left_right,
                    right_right,
                ))),
            ))),
        ))),
    ),
))))))

# --- inference state: (next-fresh-id, (substitution, failed)) ------------------------------------
# The fresh-id counter is a BinNat, so allocating and comparing type variables is O(log id).
_INITIAL_STATE: Builder = pair(BIN_ZERO, pair(_EMPTY_SUBST, FALSE))

# fresh state = ((next+1, subst, failed), TVAR next): the new state and the fresh type variable.
_FRESH: Builder = lam(lambda state: split_triple(
    state,
    lambda next_id, subst, failed: pair(
        pair(app(BIN_SUCC, next_id), pair(subst, failed)),
        app(_TVAR, next_id),
    ),
))

# unify_state state a b: apply unify to the (substitution, failed) part of the inference state.
_UNIFY_STATE: Builder = lam(lambda state: lam(lambda left_type: lam(lambda right_type: split_triple(
    state,
    lambda next_id, subst, failed: split_pair(
        ap(_UNIFY, pair(subst, failed), left_type, right_type),
        lambda new_subst, new_failed: pair(next_id, pair(new_subst, new_failed)),
    ),
))))

# lookup context index: the type at de Bruijn ``index`` in the context, as an Option.
_LOOKUP: Builder = app(Y, lam(lambda self_recursion: lam(lambda context: lam(lambda index: ap(
    context,
    _NONE,
    lam(lambda head: lam(lambda tail: ap(
        app(IS_ZERO, index),
        app(_SOME, head),
        ap(self_recursion, tail, app(PRED, index)),
    ))),
)))))

# infer state context node: infer the node's type, threading the state; returns (state, type).
# Once the state has failed (an occurs check fired), inference short-circuits: it returns a dummy type
# without recursing, so an untypable term (the compiler's Y, factorial, ...) is rejected as soon as the
# first self-application fails rather than building the whole constraint tree. This mirrors the Python
# ``_Inference.infer`` early return and is what keeps the certificate fast on the large untypable terms.
_INFER: Builder = app(Y, lam(lambda self_recursion: lam(lambda state: lam(lambda context: lam(lambda node: split_triple(
    state,
    lambda next_id, subst, failed: ap(
        failed,
        pair(state, app(_TVAR, next_id)),  # already failed: short-circuit with a dummy type
        ap(
            node,
            lam(lambda index: ap(  # QVar index
                ap(_LOOKUP, context, index),
                lam(lambda found: pair(state, found)),  # bound: its context type
                app(_FRESH, state),  # free: a fresh type variable
            )),
            lam(lambda body: split_pair(  # QLam body
                app(_FRESH, state),
                lambda state_after_fresh, parameter: split_pair(
                    ap(self_recursion, state_after_fresh, ap(_CONS, parameter, context), body),
                    lambda state_after_body, result: pair(state_after_body, ap(_TARROW, parameter, result)),
                ),
            )),
            lam(lambda function: lam(lambda argument: split_pair(  # QApp function argument
                ap(self_recursion, state, context, function),
                lambda state_after_function, function_type: split_pair(
                    ap(self_recursion, state_after_function, context, argument),
                    lambda state_after_argument, argument_type: split_pair(
                        app(_FRESH, state_after_argument),
                        lambda state_after_fresh, result: pair(
                            ap(_UNIFY_STATE, state_after_fresh, function_type, ap(_TARROW, argument_type, result)),
                            result,
                        ),
                    ),
                ),
            ))),
        ),
    ),
))))))


# TYPABLE quoted = run inference from the initial state on the empty context, read the failed flag.
# A closed term is simply typable iff inference does not fail (no occurs-check violation).
TYPABLE: Builder = lam(lambda quoted: split_pair(
    ap(_INFER, _INITIAL_STATE, _NIL, quoted),
    lambda final_state, _type: split_triple(
        final_state,
        lambda next_id, subst, failed: app(_NOT, failed),
    ),
))


# === Bottom-up principal typing: one path-free fold the interpreter tables per distinct sub-term ===
# ``TYPABLE`` above threads a fresh-id/substitution state, so the interpreter cannot share its
# per-sub-term inference (the state differs at every position) and the substitution is an O(chain)
# function. ``PRINCIPAL`` is PATH-FREE -- it takes only the node -- so ``app(PRINCIPAL, sub)`` is the
# same interned node wherever ``sub`` occurs and the interpreter tables it ONCE per distinct sub-term
# (the compiler's combinators reuse sub-combinators heavily, so this is the win). Each ``App`` unifies
# in a FRESH LOCAL substitution, resolved and discarded, so there is no global chain. Type-variable
# ids are BinNats (O(log) equality); de Bruijn indices stay Church (small, bounded by depth) and are
# converted to BinNat only where they seed a type-variable id.
#
# A result is ``(next-fresh-id, context, type, failed)``: ``context`` is a Scott list of types indexed
# by de Bruijn index (a fresh type per binder so siblings constrain them independently); ``type`` is
# the sub-term's type with the local substitution applied; ``next-fresh-id`` (a BinNat) bounds the
# type-variable ids used, so a sibling is renamed apart by adding it; ``failed`` is the occurs-check
# verdict for the whole sub-tree.

# Convert a Church numeral (a de Bruijn index from ``quote``) to a BinNat type-variable id.
_CHURCH_TO_BINNAT: Builder = lam(lambda church_value: ap(church_value, BIN_SUCC, BIN_ZERO))

# build_vars count = [TVAR 0, TVAR 1, ..., TVAR (count-1)]: the fresh context for a variable at de
# Bruijn index count-1, one distinct fresh type per enclosing binder (BinNat ids).
_BUILD_VARS_GO: Builder = app(Y, lam(lambda self_recursion: lam(lambda current: lam(lambda count: ap(
    ap(BIN_EQUAL, current, count),
    _NIL,
    ap(_CONS, app(_TVAR, current), ap(self_recursion, app(BIN_SUCC, current), count)),
)))))

_BUILD_VARS: Builder = lam(lambda count: ap(_BUILD_VARS_GO, BIN_ZERO, count))

# shift_type offset type: add ``offset`` to every type-variable id (rename a whole type apart).
_SHIFT_TYPE: Builder = app(Y, lam(lambda self_recursion: lam(lambda offset: lam(lambda type_: ap(
    type_,
    lam(lambda identifier: app(_TVAR, ap(BIN_ADD, offset, identifier))),
    lam(lambda left: lam(lambda right: ap(
        _TARROW,
        ap(self_recursion, offset, left), ap(self_recursion, offset, right),
    ))),
)))))

# shift_context offset context: rename every type in a context apart by ``offset``.
_SHIFT_CONTEXT: Builder = app(Y, lam(lambda self_recursion: lam(lambda offset: lam(lambda context: ap(
    context,
    _NIL,
    lam(lambda head: lam(lambda tail: ap(
        _CONS,
        ap(_SHIFT_TYPE, offset, head), ap(self_recursion, offset, tail),
    ))),
)))))

# apply_subst subst type: resolve ``type`` deeply, so the result carries no residual substitution.
_APPLY_SUBST: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda type_: ap(
    ap(_RESOLVE, subst, type_),
    lam(lambda identifier: app(_TVAR, identifier)),
    lam(lambda left: lam(lambda right: ap(
        _TARROW,
        ap(self_recursion, subst, left), ap(self_recursion, subst, right),
    ))),
)))))

_APPLY_SUBST_CONTEXT: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda context: ap(
    context,
    _NIL,
    lam(lambda head: lam(lambda tail: ap(
        _CONS,
        ap(_APPLY_SUBST, subst, head), ap(self_recursion, subst, tail),
    ))),
)))))

# merge state a b, state = (subst, failed): unify the shared prefix of two contexts (same de Bruijn
# indices) and keep the tail of the longer; returns (state, merged-context).
_MERGE: Builder = app(Y, lam(lambda self_recursion: lam(lambda state: lam(lambda a: lam(lambda b: ap(
    a,
    pair(state, b),  # a is nil: the merge is b
    lam(lambda head_a: lam(lambda tail_a: ap(
        b,
        pair(state, ap(_CONS, head_a, tail_a)),  # b is nil: the merge is a
        lam(lambda head_b: lam(lambda tail_b: split_pair(
            ap(self_recursion, ap(_UNIFY, state, head_a, head_b), tail_a, tail_b),
            lambda merged_state, merged_tail: pair(merged_state, ap(_CONS, head_a, merged_tail)),
        ))),
    ))),
))))))

_INITIAL_PAIR: Builder = pair(_EMPTY_SUBST, FALSE)


# principal node: the bottom-up principal typing of a quoted term, the path-free fold described above.
PRINCIPAL: Builder = app(Y, lam(lambda self_recursion: lam(lambda node: ap(
    node,
    # QVar index: context [TVAR 0 .. TVAR index], type TVAR index (ids as BinNat).
    lam(lambda index: let(app(_CHURCH_TO_BINNAT, index), lambda binnat_index: pair(
        app(BIN_SUCC, binnat_index),
        pair(
            app(_BUILD_VARS, app(BIN_SUCC, binnat_index)),
            pair(app(_TVAR, binnat_index), FALSE),
        ),
    ))),
    # QLam body: discharge de Bruijn index 0 (the binder's type) from the body's context.
    lam(lambda body: split_quad(
        app(self_recursion, body),
        lambda next_body, context_body, type_body, failed_body: ap(
            context_body,
            # body uses no enclosing binder: the parameter is a fresh, unconstrained type.
            pair(
                app(BIN_SUCC, next_body),
                pair(_NIL, pair(ap(_TARROW, app(_TVAR, next_body), type_body), failed_body)),
            ),
            lam(lambda parameter: lam(lambda rest: pair(
                next_body,
                pair(rest, pair(ap(_TARROW, parameter, type_body), failed_body)),
            ))),
        ),
    )),
    # QApp function argument: rename the argument's type-var band apart, merge the shared context,
    # then unify the function's type with (argument-type -> fresh result).
    lam(lambda function: lam(lambda argument: split_quad(
        app(self_recursion, function),
        lambda next_f, context_f, type_f, failed_f: split_quad(
            app(self_recursion, argument),
            lambda next_a, context_a, type_a, failed_a: ap(
                ap(OR, failed_f, failed_a),
                pair(
                    app(BIN_SUCC, ap(BIN_ADD, next_f, next_a)),
                    pair(_NIL, pair(app(_TVAR, BIN_ZERO), TRUE)),
                ),
                let(ap(BIN_ADD, next_f, next_a), lambda total: let(
                    ap(_SHIFT_CONTEXT, next_f, context_a), lambda context_a_shifted: let(
                    ap(_SHIFT_TYPE, next_f, type_a), lambda type_a_shifted: let(
                    app(_TVAR, total), lambda result_type: split_pair(
                        ap(_MERGE, _INITIAL_PAIR, context_f, context_a_shifted),
                        lambda merged_state, merged_context: split_pair(
                            ap(_UNIFY, merged_state, type_f, ap(_TARROW, type_a_shifted, result_type)),
                            lambda final_subst, final_failed: ap(
                                final_failed,
                                pair(
                                    app(BIN_SUCC, total),
                                    pair(_NIL, pair(app(_TVAR, BIN_ZERO), TRUE)),
                                ),
                                pair(
                                    app(BIN_SUCC, total),
                                    pair(
                                        ap(_APPLY_SUBST_CONTEXT, final_subst, merged_context),
                                        pair(ap(_APPLY_SUBST, final_subst, result_type), FALSE),
                                    ),
                                ),
                            ),
                        ),
                    )))),
                ),
            ),
        ),
    ))),
))))


# TYPABLE_BU quoted: simply typable iff the bottom-up principal typing has no occurs-check failure.
TYPABLE_BU: Builder = lam(lambda quoted: split_quad(
    app(PRINCIPAL, quoted),
    lambda next_id, context, type_, failed: app(_NOT, failed),
))
