"""COMPILE: the one specializing compiler, a single lambda term.

``COMPILE`` takes an all-in-one option and a quoted program and produces the generic Scott-encoded
Python AST. The option is a Scott tagged union destructured by applying it to three handlers:

  Specialized(island_depth) = lam s. lam w. lam n. s island_depth -> the default, specialized output
  Whole(thunked)            = lam s. lam w. lam n. w thunked      -> whole-program call-by-value/name
  Need                      = lam s. lam w. lam n. n              -> whole-program call-by-need module

The Need handler value is ``CODEGEN_NEED`` applied to the program; an unselected handler stays
unreduced under the weak-head interpreter, so the three targets coexist in the ONE lambda function.

The specialized output: a closed simply-typable WHOLE term carries the by-value certificate, so it
compiles to a strict call-by-value expression. Otherwise the term is reconstructed with
``make_var``/``make_lam``/``make_app``, splicing each maximal closed simply-typable sub-term (up to
the island depth) as ``value_island(<that sub-term compiled call-by-value>)`` and each maximal
closed normalizing-but-untypable sub-term as ``value_island_by_name(<compiled call-by-name>)``, and
the reconstruction is handed to ``interpret(...)``.

The recursion is PATH-FREE: ``reconstruct`` of a quoted sub-term depends only on the (interned)
sub-term, never on its position, so the interpreter tables it once per DISTINCT sub-term and the
result is a shared graph (a DAG), not the unfolded tree. The island certificates are likewise
path-free pure functions of the sub-term (closedness via the depth-free ``LOOSE_BOUND``; typability
via algorithm-W from the empty context, valid because an island is closed), so they too are tabled
per distinct sub-term.

This module is pure lambda calculus (one of the four strictly separated kinds): every top-level
binding is a ``Builder`` (a ``@curry``-decorated ``def`` IS a Builder, an object-level abstraction
applied with ``app``). The Python boundary (option encoding, quoting, serialization) lives in
``_specialize``.
"""

from __future__ import annotations

from co_lambda._analysis import IS_CLOSED, depth_at_most
from co_lambda._codec import church, int_to_binnat
from co_lambda._compiler import CODEGEN, CODEGEN_NEED
from co_lambda._dsl import Builder, app, curry, lam
from co_lambda._prelude import AND, FALSE, TRUE, Y
from co_lambda._pybuild import (
    INTERPRET_CODES,
    MAKE_APP_CODES,
    MAKE_LAM_CODES,
    MAKE_VAR_CODES,
    VALUE_ISLAND_BY_NAME_CODES,
    VALUE_ISLAND_CODES,
    emit_runtime_call,
    one_node,
    py_constant_int,
    two_nodes,
)
from co_lambda._reduce import NORMALIZES
from co_lambda._sugar import ap
from co_lambda._typecheck import TYPABLE, TYPABLE_BU

# The lazy-island fuel: NORMALIZES certifies a FINITE FULL normal form within this many steps, the
# same notion the lazy read-back needs to terminate. A sub-term that does not normalize within the
# fuel (a fixpoint combinator such as Y, which has no normal form) is conservatively left
# interpreted, NEVER made a lazy island; this keeps the lazy tier sound. The numeral mirrors the
# boundary's DEFAULT_FUEL in ``_specialize``.
_LAZY_ISLAND_FUEL: Builder = int_to_binnat(256)

# The whole-term by-value certificate: closed and simply typable, with NO depth bound. A whole
# typable program (however deep) compiles to a strict call-by-value value; the depth bound below is
# only for deciding which SUB-terms to splice as islands inside an interpret-headed reconstruction.
_CLOSED_TYPABLE: Builder = lam(lambda quoted: ap(AND, app(IS_CLOSED, quoted), app(TYPABLE, quoted)))


# The quoted sub-term compiled to a strict call-by-value / call-by-name expression by ``CODEGEN``
# (the option is the Church boolean ``thunked``: FALSE = eager, TRUE = lazy), from binder depth zero.
_COMPILE_CALL_BY_VALUE: Builder = lam(lambda quoted: ap(CODEGEN, FALSE, church(0), quoted))
_COMPILE_CALL_BY_NAME: Builder = lam(lambda quoted: ap(CODEGEN, TRUE, church(0), quoted))


@curry
def _island_term(depth_bound: Builder, quoted: Builder) -> Builder:
    """The per-sub-term island certificate at ``depth_bound`` (a Church numeral): closed AND shallow
    enough AND simply typable. The AND short-circuits, so TYPABLE_BU only runs on a closed, shallow
    sub-term. A bound past the deepest sub-term admits every island."""
    return ap(
        AND, app(IS_CLOSED, quoted),
        ap(AND, ap(depth_at_most, depth_bound, quoted), app(TYPABLE_BU, quoted)),
    )


@curry
def _lazy_island_term(depth_bound: Builder, quoted: Builder) -> Builder:
    """The per-sub-term LAZY island certificate at ``depth_bound``: closed AND shallow enough AND
    NORMALIZES (a finite full normal form within ``_LAZY_ISLAND_FUEL``). Tested only after the
    call-by-value certificate fails, so it fires on a closed, shallow, untypable-but-normalizing
    sub-term. The AND short-circuits, so the expensive NORMALIZES runs only on a closed (and
    shallow) sub-term."""
    return ap(
        AND, app(IS_CLOSED, quoted),
        ap(AND, ap(depth_at_most, depth_bound, quoted), ap(NORMALIZES, _LAZY_ISLAND_FUEL, quoted)),
    )


@curry
def _reconstruct(depth_bound: Builder) -> Builder:
    """reconstruct quoted -> generic Python AST at ``depth_bound``. A maximal closed simply-typable
    island becomes value_island(<call-by-value>); failing that, a maximal closed
    normalizing-but-untypable island becomes value_island_by_name(<call-by-name>) (the lazy tier);
    otherwise the node is rebuilt with make_var/make_lam/make_app, recursing. The call-by-value
    certificate is tested first (a typable term is strongly normalizing, so strict is safe); the
    lazy certificate is the sound fallback for an untypable term WITH a finite normal form."""
    return app(Y, lam(lambda self_recursion: lam(lambda quoted: ap(
        ap(_island_term, depth_bound, quoted),
        emit_runtime_call(VALUE_ISLAND_CODES, one_node(app(_COMPILE_CALL_BY_VALUE, quoted))),
        ap(
            ap(_lazy_island_term, depth_bound, quoted),
            emit_runtime_call(
                VALUE_ISLAND_BY_NAME_CODES, one_node(app(_COMPILE_CALL_BY_NAME, quoted)),
            ),
            ap(
                quoted,
                lam(lambda index: emit_runtime_call(
                    MAKE_VAR_CODES, one_node(py_constant_int(index)),
                )),
                lam(lambda body: emit_runtime_call(
                    MAKE_LAM_CODES, one_node(app(self_recursion, body)),
                )),
                lam(lambda function: lam(lambda argument: emit_runtime_call(
                    MAKE_APP_CODES,
                    two_nodes(app(self_recursion, function), app(self_recursion, argument)),
                ))),
            ),
        ),
    ))))


@curry
def _specialized_output(depth: Builder, quoted: Builder) -> Builder:
    """The locally-specialized output of ``quoted`` at island depth ``depth`` (a runtime Church
    numeral): a closed simply-typable whole term is a strict call-by-value expression; otherwise
    interpret(<reconstruction>) with the maximal islands up to ``depth`` spliced."""
    return ap(
        app(_CLOSED_TYPABLE, quoted),
        app(_COMPILE_CALL_BY_VALUE, quoted),
        emit_runtime_call(INTERPRET_CODES, one_node(ap(_reconstruct, depth, quoted))),
    )


@curry
def _whole_output(thunked: Builder, quoted: Builder) -> Builder:
    """The whole-program call-by-value/name output of ``quoted`` (``thunked`` the Church boolean),
    delegating to the code generator ``CODEGEN``."""
    return ap(CODEGEN, thunked, church(0), quoted)


COMPILE: Builder = curry(lambda option, quoted: ap(
    option,
    lam(lambda depth: ap(_specialized_output, depth, quoted)),
    lam(lambda thunked: ap(_whole_output, thunked, quoted)),
    app(CODEGEN_NEED, quoted),
))


# CHOOSE_RUNTIME fuel quoted: the runtime tag (a Church numeral) certified to preserve the term's
# interpreted behaviour. Closed and simply typable -> call-by-value (tag 0, strongly normalizing so
# strict is safe); else a finite normal form within the fuel -> call-by-need (tag 1, the lazy regime
# is viable and call-by-need shares); else interpret (tag 2). The Church if is lazy, so the
# expensive NORMALIZES branch is only reached for an untypable term. The whole decision is the
# lambda term; the boundary only reads the tag back as a Runtime label.
CHOOSE_RUNTIME: Builder = lam(lambda fuel: lam(lambda quoted: ap(
    ap(AND, app(IS_CLOSED, quoted), app(TYPABLE, quoted)),
    church(0),
    ap(
        ap(NORMALIZES, fuel, quoted),
        church(1),
        church(2),
    ),
)))
