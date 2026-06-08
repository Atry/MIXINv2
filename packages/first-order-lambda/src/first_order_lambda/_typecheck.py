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

from first_order_lambda._ast import Node, make_app, make_var
from first_order_lambda._binnat import BIN_EQUAL, BIN_SUCC, BIN_ZERO
from first_order_lambda._compiler import Z, _recursion_headroom, quote
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import FALSE, IS_ZERO, OR, PRED, TRUE
from first_order_lambda._shape import VarShape


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
_RESOLVE: Builder = app(Z, lam(lambda self_recursion: lam(lambda subst: lam(lambda type_: _match_type(
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
_OCCURS: Builder = app(Z, lam(lambda self_recursion: lam(lambda subst: lam(lambda identifier: lam(lambda type_: _let(
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
_UNIFY: Builder = app(Z, lam(lambda self_recursion: lam(lambda state: lam(lambda left_type: lam(lambda right_type: _split(
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
_LOOKUP: Builder = app(Z, lam(lambda self_recursion: lam(lambda context: lam(lambda index: _ap(
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
# without recursing, so an untypable term (the compiler's Z, factorial, ...) is rejected as soon as the
# first self-application fails rather than building the whole constraint tree. This mirrors the Python
# ``_Inference.infer`` early return and is what keeps the certificate fast on the large untypable terms.
_INFER: Builder = app(Z, lam(lambda self_recursion: lam(lambda state: lam(lambda context: lam(lambda node: _split_state(
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
