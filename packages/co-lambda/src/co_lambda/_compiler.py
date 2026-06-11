"""The code generators, written in the pure lambda calculus.

The source is a quoted lambda term, a Scott value over ``QVar i`` / ``QLam body`` / ``QApp f a`` (de
Bruijn). ``CODEGEN`` is a pure lambda term that, GIVEN a compilation option, maps the quoted source to
the generic Scott-encoded Python AST (the same encoding ``_pyast`` derives by reflection on ``ast``: a
``Name``/``Lambda``/``Call`` spine for the expression targets, a ``Module`` of memoising-thunk defs for
call-by-need). The option decides the target, in the lambda term itself: under the call-by-value option
an application is a strict call and a variable is a bare name; under the call-by-name option a variable
is forced and an argument is thunked (``force``/``Thunk``), matching the interpreter's weak-head
reduction. ``CODEGEN_NEED`` is the whole-program call-by-need module target (explicit memoising
thunks). The one specializing compiler ``COMPILE`` that applies these lives in ``_compile_term``.

This module is pure lambda calculus (one of the four strictly separated kinds: codec / sugar /
runtime / pure-lambda source): every top-level binding is a ``Builder``, written through the
``_dsl``/``_sugar``/``_pybuild`` notation with ``_codec`` literal renderings. The compiler's own
recursion is the ordinary fixpoint ``Y``: its source never assumes a strict target (a Y-containing
sub-term is untypable, so the specializer never sends it to the call-by-value target, and a lazy
island's call-by-name/need Python thunks the recursion, where Y converges), so the eta-expanded
strict variant Z is not used anywhere in this codebase.
"""

from __future__ import annotations

from co_lambda._codec import char_codes, church
from co_lambda._dsl import Builder, app, lam
from co_lambda._prelude import SCOTT_NIL, SUCC, Y
from co_lambda._pybuild import (
    depth_ident,
    ex_app,
    ex_force,
    ex_name,
    field_str,
    level_ident,
    name_symbol_field,
    py_call,
    py_lambda,
    py_lambda0,
    py_module,
    single_arg,
    st_assign,
    st_func_def,
    st_return,
    stmt,
    thunk_scaffold,
)
from co_lambda._sugar import ap, cons, let, one, pair, pair_first, pair_second, two

# Target wrappers, selected by the option (a Church boolean ``thunked``): the call-by-name target wraps
# a variable and a function in ``force(...)`` and an argument in ``Thunk(lambda: ...)``; call-by-value
# wraps with identity.
_FORCE_NAME: Builder = ex_name(field_str(char_codes("force")))
_THUNK_NAME: Builder = ex_name(field_str(char_codes("Thunk")))
_FORCE_WRAP: Builder = lam(lambda expr: py_call(_FORCE_NAME, single_arg(expr)))
_THUNK_WRAP: Builder = lam(lambda expr: py_call(_THUNK_NAME, single_arg(py_lambda0(expr))))
_IDENTITY_WRAP: Builder = lam(lambda expr: expr)

# CODEGEN (call-by-value / call-by-name): self depth quoted -> Scott Python EXPRESSION. Variables are
# named by binder DEPTH (a one-element Nat list, rendered by the one _pyast decoder): the binder at
# depth d is ``v_d`` and ``QVar i`` under d enclosing binders is ``v_{d-1-i}`` (Church truncated
# subtraction). Depth naming keeps the recursion PATH-FREE: the call spine ``self depth quoted`` is
# interned per (depth, sub-term), so the interpreter tables compilation once per distinct sub-term and
# depth. (CODEGEN_NEED below still threads a path: its per-node memo cells and thunk defs are
# statements that need per-occurrence unique names.) The option (a Church boolean ``thunked``) selects
# the wraps: call-by-name forces a variable/function and thunks an argument; call-by-value wraps with
# identity.
#   QVar i      -> wrapVar (Name v_{depth-1-i})
#   QLam b      -> Lambda (v_<depth>) (self (succ depth) b)
#   QApp f a    -> Call (wrapFun (self depth f)) [wrapArg (self depth a)]
CODEGEN: Builder = lam(lambda thunked: app(
    Y,
    lam(lambda self_recursion: lam(lambda depth: lam(lambda quoted: ap(
        quoted,
        lam(lambda index: app(
            ap(thunked, _FORCE_WRAP, _IDENTITY_WRAP),
            ex_name(level_ident(depth, index)),
        )),
        lam(lambda body: py_lambda(
            depth_ident(depth),
            ap(self_recursion, app(SUCC, depth), body),
        )),
        lam(lambda function: lam(lambda argument: py_call(
            app(
                ap(thunked, _FORCE_WRAP, _IDENTITY_WRAP),
                ap(self_recursion, depth, function),
            ),
            single_arg(app(
                ap(thunked, _THUNK_WRAP, _IDENTITY_WRAP),
                ap(self_recursion, depth, argument),
            )),
        ))),
    ))))
))


# --- call-by-need: explicit memoising thunks, emitted entirely by the CODEGEN_NEED lambda term ---
# Call-by-need adds sharing to call-by-name: a thunk computes once and caches. The cache and its
# update need statements, so the target is statement-based, and the WHOLE structure (the def, the
# nonlocal, the sentinel guard, the assignment, the return, the module wrapper) is emitted by the
# CODEGEN_NEED lambda term as a Scott-encoded Python AST. Every sub-term compiles to a memoising
# thunk:
#
#     v_<cell> = CALL_BY_NEED_SENTINEL
#     def v_<thunk>():
#         nonlocal v_<cell>
#         if v_<cell> is CALL_BY_NEED_SENTINEL:
#             <compute statements>
#             v_<cell> = <compute expression>
#         return v_<cell>
#
# Forcing a thunk is calling it; a bound variable arrives as a thunk and is forced on use; a lambda's
# value is an inner ``def v_<func>(v_<param>)``. Every identifier is a SYMBOL: the path of the AST
# node it belongs to, a list of Church-numeral segments (a branch index per descent, plus a kind tag),
# decoded to an underscore-joined name that is unique by construction. A binder's symbol is threaded
# down in an environment so a variable looks up its binder's name by de Bruijn index. The program is
# wrapped in ``def _program(): ...; return <root thunk>`` so the ``nonlocal`` cells have an enclosing
# function scope, and ``program = _program()`` binds it.

# Path segments: a branch index per descent (function/argument/lambda-body) and a kind tag per role.
_BRANCH_FUNCTION: Builder = church(0)
_BRANCH_ARGUMENT: Builder = church(1)
_BRANCH_BODY: Builder = church(2)
_KIND_THUNK: Builder = church(0)
_KIND_CELL: Builder = church(1)
_KIND_FUNCTION: Builder = church(2)
_KIND_VARIABLE: Builder = church(3)

# append xs ys = xs (lambda h. lambda t. cons h (self t ys)) ys, by Scott-list elimination.
_APPEND: Builder = app(Y, lam(lambda self_recursion: lam(lambda xs: lam(lambda ys: app(
    app(xs, lam(lambda head: lam(lambda tail: cons(head, ap(self_recursion, tail, ys))))),
    ys,
)))))

# tail/head by Scott-list elimination; nth drops ``index`` heads (Church iteration) then takes head.
_TAIL: Builder = lam(lambda lst: app(app(lst, lam(lambda head: lam(lambda tail: tail))), SCOTT_NIL))
_HEAD: Builder = lam(lambda lst: app(app(lst, lam(lambda head: lam(lambda tail: head))), SCOTT_NIL))
_NTH: Builder = lam(lambda index: lam(lambda env: app(_HEAD, app(app(index, _TAIL), env))))

_PROGRAM_DEF_CODES: Builder = char_codes("_program")
_PROGRAM_BIND_CODES: Builder = char_codes("program")

# The recursion: self path env quoted -> (setup statements, value expression). ``path`` is the AST
# address (Church segments, innermost first); ``env`` is the list of in-scope binder symbols.
_CODEGEN_NEED_REC: Builder = app(Y, lam(lambda self_recursion: lam(lambda path: lam(lambda env: lam(
    lambda quoted: ap(
        quoted,
        # QVar index: the variable is its binder's thunk, looked up by de Bruijn index; no setup.
        lam(lambda index: pair(SCOTT_NIL, ex_name(ap(_NTH, index, env)))),
        # QLam body: the value is an inner function; wrap it in a memoising thunk.
        lam(lambda body: let(
            name_symbol_field(_KIND_VARIABLE, path),
            lambda parameter: let(
                ap(self_recursion, cons(_BRANCH_BODY, path), cons(parameter, env), body),
                lambda compiled_body: pair(
                    thunk_scaffold(
                        name_symbol_field(_KIND_CELL, path),
                        name_symbol_field(_KIND_THUNK, path),
                        two(
                            stmt(st_func_def(
                                name_symbol_field(_KIND_FUNCTION, path),
                                one(parameter),
                                ap(
                                    _APPEND,
                                    pair_first(compiled_body),
                                    one(stmt(st_return(pair_second(compiled_body)))),
                                ),
                            )),
                            stmt(st_assign(
                                name_symbol_field(_KIND_CELL, path),
                                ex_name(name_symbol_field(_KIND_FUNCTION, path)),
                            )),
                        ),
                    ),
                    ex_name(name_symbol_field(_KIND_THUNK, path)),
                ),
            ),
        )),
        # QApp f a: force the function and apply the argument thunk; the result is a memoising thunk.
        lam(lambda function: lam(lambda argument: let(
            ap(self_recursion, cons(_BRANCH_FUNCTION, path), env, function),
            lambda compiled_function: let(
                ap(self_recursion, cons(_BRANCH_ARGUMENT, path), env, argument),
                lambda compiled_argument: pair(
                    thunk_scaffold(
                        name_symbol_field(_KIND_CELL, path),
                        name_symbol_field(_KIND_THUNK, path),
                        ap(
                            _APPEND,
                            pair_first(compiled_function),
                            ap(
                                _APPEND,
                                pair_first(compiled_argument),
                                one(stmt(st_assign(
                                    name_symbol_field(_KIND_CELL, path),
                                    # Force to WHNF: applying the function returns the body thunk, which
                                    # must itself be forced so this cell holds a value, not a thunk.
                                    ex_force(ex_app(
                                        ex_force(pair_second(compiled_function)),
                                        pair_second(compiled_argument),
                                    )),
                                ))),
                            ),
                        ),
                    ),
                    ex_name(name_symbol_field(_KIND_THUNK, path)),
                ),
            ),
        ))),
    ),
)))))


# CODEGEN_NEED wraps the root's (statements, value) in def _program(): ...; return value, then
# program = _program(), all as a generic Scott ``ast.Module``.
CODEGEN_NEED: Builder = lam(lambda quoted: let(
    ap(_CODEGEN_NEED_REC, SCOTT_NIL, SCOTT_NIL, quoted),
    lambda root: py_module(two(
        stmt(st_func_def(
            field_str(_PROGRAM_DEF_CODES),
            SCOTT_NIL,
            ap(_APPEND, pair_first(root), one(stmt(st_return(pair_second(root))))),
        )),
        stmt(st_assign(
            field_str(_PROGRAM_BIND_CODES),
            ex_force(ex_name(field_str(_PROGRAM_DEF_CODES))),
        )),
    )),
))
