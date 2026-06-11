"""Simple-typability as a lambda term: algorithm-W (STLC) written in the pure calculus.

This is the soundness certificate the specializer needs, lifted out of Python into a lambda term in
the same style as ``_analysis.CLOSED``. ``TYPABLE`` consumes a quoted term (the ``QVar``/``QLam``/``QApp``
Scott value ``quote`` produces) and returns a Church boolean: whether the term is simply typable, which
is a sound certificate of strong normalization (so the strict call-by-value runtime is safe). The
Python ``_specialize._Inference`` is the specification this ports and the test oracle it is checked
against; it is no longer on the compile path.

The encoding is monomorphic algorithm-W (one fresh monotype per binder, no generalization), threading
a state of ``(next-fresh-id, substitution, failed-flag)`` purely:

* Types are a two-constructor Scott value: ``TVAR id`` (``id`` a BinNat, so allocating and comparing
  type variables is O(log id), letting a large island with hundreds of variables type fast) and
  ``TARROW l r``.
* The substitution is a function ``id -> Option Type`` (the empty map is ``lambda id. NONE``; extension
  shadows by id-equality), so ``resolve`` follows the chain and ``occurs`` walks the resolved type.
* ``unify`` threads ``(substitution, failed)`` and sets ``failed`` when the occurs check fires, which is
  exactly why the self-application ``x x`` (constraint ``alpha = alpha -> beta``) is untypable.
* ``infer`` threads the whole state and returns ``(state, type)``; a binder extends the typing context
  (a Scott list indexed by de Bruijn index) with a fresh monotype. It short-circuits once failed, so an
  untypable term is rejected as soon as the first occurs check fires (this keeps it fast on large terms).

Termination: ``infer`` recurses structurally on the term; the occurs check keeps the substitution
acyclic, so ``resolve``/``occurs``/``unify`` recurse on finite type trees. The verdict is therefore a
normal-form Church boolean the interpreter reads back.
"""

from __future__ import annotations

from co_lambda._ast import Node, make_app, make_var
from co_lambda._binnat import BIN_ADD, BIN_EQUAL, BIN_SUCC, BIN_ZERO
from co_lambda._compiler import _recursion_headroom, quote
from co_lambda._dsl import Builder, app, build, lam
from co_lambda._prelude import FALSE, IS_ZERO, OR, PRED, TRUE, Y
from co_lambda._shape import VarShape


def _ap(function: Builder, *arguments: Builder) -> Builder:
    """Left-folded application: ``_ap(f, x, y, z)`` is ``((f x) y) z``."""
    result = function
    for argument in arguments:
        result = app(result, argument)
    return result


def _let(value: Builder, body) -> Builder:
    """Bind ``value`` for ``body`` (a Python ``lambda`` over the bound Builder)."""
    return app(lam(body), value)


# --- booleans and type-variable id equality ------------------------------------------------------
_NOT: Builder = lam(lambda boolean: _ap(boolean, FALSE, TRUE))


def _equal(a: Builder, b: Builder) -> Builder:
    """Equality of two type-variable ids. Ids are BinNats (binary naturals), so equality is O(log id),
    not the O(id) of a Church-numeral comparison: this is what lets a large island, which needs
    hundreds of fresh type variables, be type-checked in seconds rather than timing out."""
    return _ap(BIN_EQUAL, a, b)


def _or(a: Builder, b: Builder) -> Builder:
    return _ap(OR, a, b)


def _choose(boolean: Builder, when_true: Builder, when_false: Builder) -> Builder:
    """A Church-boolean if-then-else."""
    return _ap(boolean, when_true, when_false)


# --- pairs, options, lists (destructured with continuations, no projections) ---------------------
_PAIR: Builder = lam(lambda first: lam(lambda second: lam(lambda consume: _ap(consume, first, second))))


def _pair(first: Builder, second: Builder) -> Builder:
    return _ap(_PAIR, first, second)


def _split(pair_value: Builder, body) -> Builder:
    """Destructure a ``_pair`` for ``body`` (a Python ``lambda`` over the two bound Builders)."""
    return app(pair_value, lam(lambda first: lam(lambda second: body(first, second))))


# Option: SOME carries a value, NONE is empty; consumed as ``option some_handler none_value``.
_SOME: Builder = lam(lambda value: lam(lambda some_handler: lam(lambda none_value: app(some_handler, value))))
_NONE: Builder = lam(lambda some_handler: lam(lambda none_value: none_value))


def _option(option_value: Builder, some_handler: Builder, none_value: Builder) -> Builder:
    return _ap(option_value, some_handler, none_value)


# Scott list: consumed as ``list nil_value cons_handler``.
_NIL: Builder = lam(lambda nil_value: lam(lambda cons_handler: nil_value))
_CONS: Builder = lam(lambda head: lam(lambda tail: lam(lambda nil_value: lam(lambda cons_handler: _ap(cons_handler, head, tail)))))


def _cons(head: Builder, tail: Builder) -> Builder:
    return _ap(_CONS, head, tail)


# --- types: TVAR id | TARROW left right (consumed as ``type var_handler arrow_handler``) ----------
_TVAR: Builder = lam(lambda identifier: lam(lambda var_handler: lam(lambda arrow_handler: app(var_handler, identifier))))
_TARROW: Builder = lam(lambda left: lam(lambda right: lam(lambda var_handler: lam(lambda arrow_handler: _ap(arrow_handler, left, right)))))


def _tvar(identifier: Builder) -> Builder:
    return app(_TVAR, identifier)


def _tarrow(left: Builder, right: Builder) -> Builder:
    return _ap(_TARROW, left, right)


def _match_type(type_: Builder, var_handler: Builder, arrow_handler: Builder) -> Builder:
    return _ap(type_, var_handler, arrow_handler)


# --- substitution: a function id -> Option Type --------------------------------------------------
_EMPTY_SUBST: Builder = lam(lambda identifier: _NONE)
# extend subst id type = a new map shadowing ``id`` with ``SOME type``.
_EXTEND: Builder = lam(lambda subst: lam(lambda identifier: lam(lambda bound: lam(lambda lookup: _choose(
    _equal(lookup, identifier),
    app(_SOME, bound),
    app(subst, lookup),
)))))


def _extend(subst: Builder, identifier: Builder, bound: Builder) -> Builder:
    return _ap(_EXTEND, subst, identifier, bound)


# resolve subst type: follow the substitution chain to the representative type.
_RESOLVE: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda type_: _match_type(
    type_,
    lam(lambda identifier: _option(
        app(subst, identifier),
        lam(lambda found: _ap(self_recursion, subst, found)),
        _tvar(identifier),
    )),
    lam(lambda left: lam(lambda right: _tarrow(left, right))),
)))))


def _resolve(subst: Builder, type_: Builder) -> Builder:
    return _ap(_RESOLVE, subst, type_)


# occurs subst id type: whether ``id`` occurs in the resolved ``type`` (the occurs check).
_OCCURS: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda identifier: lam(lambda type_: _let(
    _resolve(subst, type_),
    lambda resolved: _match_type(
        resolved,
        lam(lambda other: _equal(other, identifier)),
        lam(lambda left: lam(lambda right: _or(
            _ap(self_recursion, subst, identifier, left),
            _ap(self_recursion, subst, identifier, right),
        ))),
    ),
))))))


def _occurs(subst: Builder, identifier: Builder, type_: Builder) -> Builder:
    return _ap(_OCCURS, subst, identifier, type_)


# bind subst id type: if the occurs check fires, fail; else extend the substitution. The result is a
# pair (substitution, failed).
_BIND: Builder = lam(lambda subst: lam(lambda identifier: lam(lambda bound: _choose(
    _occurs(subst, identifier, bound),
    _pair(subst, TRUE),
    _pair(_extend(subst, identifier, bound), FALSE),
))))


def _bind(subst: Builder, identifier: Builder, bound: Builder) -> Builder:
    return _ap(_BIND, subst, identifier, bound)


# unify state a b, with state = (substitution, failed): unify the two types, threading the state.
# Short-circuits when already failed; otherwise resolves both sides and matches the four shape cases:
# var/var (equal: nothing; else bind), var/arrow and arrow/var (bind after occurs check), arrow/arrow
# (unify the components left to right).
_UNIFY: Builder = app(Y, lam(lambda self_recursion: lam(lambda state: lam(lambda left_type: lam(lambda right_type: _split(
    state,
    lambda subst, failed: _choose(
        failed,
        state,
        _let(_resolve(subst, left_type), lambda left: _let(_resolve(subst, right_type), lambda right: _match_type(
            left,
            lam(lambda left_id: _match_type(
                right,
                lam(lambda right_id: _choose(_equal(left_id, right_id), state, _bind(subst, left_id, right))),
                lam(lambda right_left: lam(lambda right_right: _bind(subst, left_id, right))),
            )),
            lam(lambda left_left: lam(lambda left_right: _match_type(
                right,
                lam(lambda right_id: _bind(subst, right_id, left)),
                lam(lambda right_left: lam(lambda right_right: _ap(
                    self_recursion,
                    _ap(self_recursion, state, left_left, right_left),
                    left_right,
                    right_right,
                ))),
            ))),
        ))),
    ),
))))))


def _unify(state: Builder, left_type: Builder, right_type: Builder) -> Builder:
    return _ap(_UNIFY, state, left_type, right_type)


# --- inference state: (next-fresh-id, (substitution, failed)) ------------------------------------
def _make_state(next_id: Builder, subst: Builder, failed: Builder) -> Builder:
    return _pair(next_id, _pair(subst, failed))


def _split_state(state: Builder, body) -> Builder:
    """Destructure an inference state for ``body`` (a Python ``lambda`` over next-id, subst, failed)."""
    return _split(state, lambda next_id, rest: _split(rest, lambda subst, failed: body(next_id, subst, failed)))


# The fresh-id counter is a BinNat, so allocating and comparing type variables is O(log id).
_INITIAL_STATE: Builder = _make_state(BIN_ZERO, _EMPTY_SUBST, FALSE)

# fresh state = ((next+1, subst, failed), TVAR next): the new state and the fresh type variable.
_FRESH: Builder = lam(lambda state: _split_state(
    state,
    lambda next_id, subst, failed: _pair(
        _make_state(app(BIN_SUCC, next_id), subst, failed),
        _tvar(next_id),
    ),
))


def _fresh(state: Builder) -> Builder:
    return app(_FRESH, state)


# unify_state state a b: apply unify to the (substitution, failed) part of the inference state.
_UNIFY_STATE: Builder = lam(lambda state: lam(lambda left_type: lam(lambda right_type: _split_state(
    state,
    lambda next_id, subst, failed: _split(
        _unify(_pair(subst, failed), left_type, right_type),
        lambda new_subst, new_failed: _make_state(next_id, new_subst, new_failed),
    ),
))))


def _unify_state(state: Builder, left_type: Builder, right_type: Builder) -> Builder:
    return _ap(_UNIFY_STATE, state, left_type, right_type)


# lookup context index: the type at de Bruijn ``index`` in the context, as an Option.
_LOOKUP: Builder = app(Y, lam(lambda self_recursion: lam(lambda context: lam(lambda index: _ap(
    context,
    _NONE,
    lam(lambda head: lam(lambda tail: _choose(
        app(IS_ZERO, index),
        app(_SOME, head),
        _ap(self_recursion, tail, app(PRED, index)),
    ))),
)))))


def _lookup(context: Builder, index: Builder) -> Builder:
    return _ap(_LOOKUP, context, index)


# infer state context node: infer the node's type, threading the state; returns (state, type).
# Once the state has failed (an occurs check fired), inference short-circuits: it returns a dummy type
# without recursing, so an untypable term (the compiler's Y, factorial, ...) is rejected as soon as the
# first self-application fails rather than building the whole constraint tree. This mirrors the Python
# ``_Inference.infer`` early return and is what keeps the certificate fast on the large untypable terms.
_INFER: Builder = app(Y, lam(lambda self_recursion: lam(lambda state: lam(lambda context: lam(lambda node: _split_state(
    state,
    lambda next_id, subst, failed: _choose(
        failed,
        _pair(state, _tvar(next_id)),  # already failed: short-circuit with a dummy type
        _ap(
            node,
            lam(lambda index: _option(  # QVar index
                _lookup(context, index),
                lam(lambda found: _pair(state, found)),  # bound: its context type
                _fresh(state),  # free: a fresh type variable
            )),
            lam(lambda body: _split(  # QLam body
                _fresh(state),
                lambda state_after_fresh, parameter: _split(
                    _ap(self_recursion, state_after_fresh, _cons(parameter, context), body),
                    lambda state_after_body, result: _pair(state_after_body, _tarrow(parameter, result)),
                ),
            )),
            lam(lambda function: lam(lambda argument: _split(  # QApp function argument
                _ap(self_recursion, state, context, function),
                lambda state_after_function, function_type: _split(
                    _ap(self_recursion, state_after_function, context, argument),
                    lambda state_after_argument, argument_type: _split(
                        _fresh(state_after_argument),
                        lambda state_after_fresh, result: _pair(
                            _unify_state(state_after_fresh, function_type, _tarrow(argument_type, result)),
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
TYPABLE: Builder = lam(lambda quoted: _split(
    _ap(_INFER, _INITIAL_STATE, _NIL, quoted),
    lambda final_state, _type: _split_state(
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


def _church_to_binnat(church_value: Builder) -> Builder:
    """Convert a Church numeral (a de Bruijn index from ``quote``) to a BinNat type-variable id."""
    return _ap(church_value, BIN_SUCC, BIN_ZERO)


def _plus(a: Builder, b: Builder) -> Builder:
    return _ap(BIN_ADD, a, b)


def _result(next_id: Builder, context: Builder, type_: Builder, failed: Builder) -> Builder:
    return _pair(next_id, _pair(context, _pair(type_, failed)))


def _split_result(result: Builder, body) -> Builder:
    """Destructure a principal-typing result for ``body`` (next-id, context, type, failed)."""
    return _split(result, lambda next_id, rest1: _split(
        rest1, lambda context, rest2: _split(rest2, lambda type_, failed: body(next_id, context, type_, failed)),
    ))


# build_vars count = [TVAR 0, TVAR 1, ..., TVAR (count-1)]: the fresh context for a variable at de
# Bruijn index count-1, one distinct fresh type per enclosing binder (BinNat ids).
_BUILD_VARS_GO: Builder = app(Y, lam(lambda self_recursion: lam(lambda current: lam(lambda count: _choose(
    _equal(current, count),
    _NIL,
    _cons(_tvar(current), _ap(self_recursion, app(BIN_SUCC, current), count)),
)))))


def _build_vars(count: Builder) -> Builder:
    return _ap(_BUILD_VARS_GO, BIN_ZERO, count)


# shift_type offset type: add ``offset`` to every type-variable id (rename a whole type apart).
_SHIFT_TYPE: Builder = app(Y, lam(lambda self_recursion: lam(lambda offset: lam(lambda type_: _match_type(
    type_,
    lam(lambda identifier: _tvar(_plus(offset, identifier))),
    lam(lambda left: lam(lambda right: _tarrow(
        _ap(self_recursion, offset, left), _ap(self_recursion, offset, right),
    ))),
)))))


def _shift_type(offset: Builder, type_: Builder) -> Builder:
    return _ap(_SHIFT_TYPE, offset, type_)


# shift_context offset context: rename every type in a context apart by ``offset``.
_SHIFT_CONTEXT: Builder = app(Y, lam(lambda self_recursion: lam(lambda offset: lam(lambda context: _ap(
    context,
    _NIL,
    lam(lambda head: lam(lambda tail: _cons(_shift_type(offset, head), _ap(self_recursion, offset, tail)))),
)))))


def _shift_context(offset: Builder, context: Builder) -> Builder:
    return _ap(_SHIFT_CONTEXT, offset, context)


# apply_subst subst type: resolve ``type`` deeply, so the result carries no residual substitution.
_APPLY_SUBST: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda type_: _match_type(
    _resolve(subst, type_),
    lam(lambda identifier: _tvar(identifier)),
    lam(lambda left: lam(lambda right: _tarrow(
        _ap(self_recursion, subst, left), _ap(self_recursion, subst, right),
    ))),
)))))


def _apply_subst(subst: Builder, type_: Builder) -> Builder:
    return _ap(_APPLY_SUBST, subst, type_)


_APPLY_SUBST_CONTEXT: Builder = app(Y, lam(lambda self_recursion: lam(lambda subst: lam(lambda context: _ap(
    context,
    _NIL,
    lam(lambda head: lam(lambda tail: _cons(_apply_subst(subst, head), _ap(self_recursion, subst, tail)))),
)))))


def _apply_subst_context(subst: Builder, context: Builder) -> Builder:
    return _ap(_APPLY_SUBST_CONTEXT, subst, context)


# merge state a b, state = (subst, failed): unify the shared prefix of two contexts (same de Bruijn
# indices) and keep the tail of the longer; returns (state, merged-context).
_MERGE: Builder = app(Y, lam(lambda self_recursion: lam(lambda state: lam(lambda a: lam(lambda b: _ap(
    a,
    _pair(state, b),  # a is nil: the merge is b
    lam(lambda head_a: lam(lambda tail_a: _ap(
        b,
        _pair(state, _cons(head_a, tail_a)),  # b is nil: the merge is a
        lam(lambda head_b: lam(lambda tail_b: _split(
            _ap(self_recursion, _unify(state, head_a, head_b), tail_a, tail_b),
            lambda merged_state, merged_tail: _pair(merged_state, _cons(head_a, merged_tail)),
        ))),
    ))),
))))))


def _merge(state: Builder, a: Builder, b: Builder) -> Builder:
    return _ap(_MERGE, state, a, b)


_INITIAL_PAIR: Builder = _pair(_EMPTY_SUBST, FALSE)


# principal node: the bottom-up principal typing of a quoted term, the path-free fold described above.
PRINCIPAL: Builder = app(Y, lam(lambda self_recursion: lam(lambda node: _ap(
    node,
    # QVar index: context [TVAR 0 .. TVAR index], type TVAR index (ids as BinNat).
    lam(lambda index: _let(_church_to_binnat(index), lambda binnat_index: _result(
        app(BIN_SUCC, binnat_index), _build_vars(app(BIN_SUCC, binnat_index)), _tvar(binnat_index), FALSE,
    ))),
    # QLam body: discharge de Bruijn index 0 (the binder's type) from the body's context.
    lam(lambda body: _split_result(
        app(self_recursion, body),
        lambda next_body, context_body, type_body, failed_body: _ap(
            context_body,
            # body uses no enclosing binder: the parameter is a fresh, unconstrained type.
            _result(app(BIN_SUCC, next_body), _NIL, _tarrow(_tvar(next_body), type_body), failed_body),
            lam(lambda parameter: lam(lambda rest: _result(
                next_body, rest, _tarrow(parameter, type_body), failed_body,
            ))),
        ),
    )),
    # QApp function argument: rename the argument's type-var band apart, merge the shared context,
    # then unify the function's type with (argument-type -> fresh result).
    lam(lambda function: lam(lambda argument: _split_result(
        app(self_recursion, function),
        lambda next_f, context_f, type_f, failed_f: _split_result(
            app(self_recursion, argument),
            lambda next_a, context_a, type_a, failed_a: _choose(
                _or(failed_f, failed_a),
                _result(app(BIN_SUCC, _plus(next_f, next_a)), _NIL, _tvar(BIN_ZERO), TRUE),
                _let(_plus(next_f, next_a), lambda total: _let(
                    _shift_context(next_f, context_a), lambda context_a_shifted: _let(
                    _shift_type(next_f, type_a), lambda type_a_shifted: _let(
                    _tvar(total), lambda result_type: _split(
                        _merge(_INITIAL_PAIR, context_f, context_a_shifted),
                        lambda merged_state, merged_context: _split(
                            _unify(merged_state, type_f, _tarrow(type_a_shifted, result_type)),
                            lambda final_subst, final_failed: _choose(
                                final_failed,
                                _result(app(BIN_SUCC, total), _NIL, _tvar(BIN_ZERO), TRUE),
                                _result(
                                    app(BIN_SUCC, total),
                                    _apply_subst_context(final_subst, merged_context),
                                    _apply_subst(final_subst, result_type),
                                    FALSE,
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
TYPABLE_BU: Builder = lam(lambda quoted: _split_result(
    app(PRINCIPAL, quoted),
    lambda next_id, context, type_, failed: app(_NOT, failed),
))


_TRUE_MARKER = 7_200_001
_FALSE_MARKER = 7_200_002


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


def is_typable_lambda(node: Node) -> bool:
    """Whether ``node`` is simply typable, decided by running the lambda-level ``TYPABLE`` analysis.

    The verdict is computed by the interpreter from the quoted term, so the typability certificate that
    drives specialization is itself a lambda term, not Python code. This is the lambda port of
    ``_specialize.is_typable`` (algorithm-W), which remains as the specification and the test oracle.
    """
    with _recursion_headroom():
        verdict = build(app(TYPABLE, quote(node)))
        return _interpret_boolean(verdict)


def typable_bu_lambda(node: Node) -> bool:
    """Whether ``node`` is simply typable, decided by the path-free bottom-up fold ``TYPABLE_BU``.

    ``PRINCIPAL`` types every distinct sub-term once (the interpreter tables it, since it is path-free)
    and reconciles locally per application, so it shares work across the term DAG that the state-
    threading ``TYPABLE`` cannot. This is the certificate the island specializer is intended to consult;
    ``_specialize.is_typable`` remains the oracle it is checked against.
    """
    with _recursion_headroom():
        verdict = build(app(TYPABLE_BU, quote(node)))
        return _interpret_boolean(verdict)
