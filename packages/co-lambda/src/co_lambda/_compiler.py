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
    lifted_call,
    lifted_factory,
    name_gensym_field,
    one_node,
    py_add,
    py_call,
    py_constant_int,
    py_lambda,
    py_lambda0,
    py_module,
    py_subscript,
    py_tuple,
    single_arg,
    st_assign,
    st_func_def,
    st_return,
    stmt,
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


# --- call-by-need: lambda-lifted memoising-thunk factories, emitted by the CODEGEN_NEED lambda term ---
# Call-by-need adds sharing to call-by-name: a thunk computes once and caches. The cache and its update
# need statements, so the target is a module of top-level factory functions, one per DISTINCT sub-term.
# Each sub-term S at binder depth d compiles to a top-level factory that takes the ENVIRONMENT of the
# enclosing binder thunks (a tuple ``env = (v_0, ..., v_{d-1})``) as its SINGLE parameter and returns a
# fresh memoising thunk:
#
#     def mk_<S>(env):
#         <cell> = CALL_BY_NEED_SENTINEL
#         def <thunk>():
#             nonlocal <cell>
#             if <cell> is CALL_BY_NEED_SENTINEL:
#                 <cell> = <compute, referencing env[level] and other mk_<child>(env) calls>
#             return <cell>
#         return <thunk>
#
# An OCCURRENCE of S is the value expression ``mk_<S>(<env>)`` -- a call passing the in-scope environment.
# This is STG-style lambda-lifting: because every factory is self-contained (it captures nothing
# lexically; its free variables arrive in ``env``), the SAME distinct (depth, sub-term) emits the SAME
# factory text wherever it occurs, so the serializer can drop the byte-identical duplicates and emit each
# factory ONCE. The earlier nested scheme inlined a sub-term's whole thunk scaffold at every occurrence,
# unfolding a shared term graph into the output (COMPILE's ~19x sharing -> a ~482MB module); lambda-
# lifting keeps the output linear in the DISTINCT sub-terms. Crucially the environment is ONE parameter,
# not the d binders spread out: an explicit ``v_0, ..., v_{d-1}`` parameter (and argument) list is O(d)
# per node, so for COMPILE's depth ~227 the generation was O(distinct * depth^2) and blew past 20 GB; a
# single ``env`` keeps every node O(1). A variable ``QVar i`` reads ``env[d-1-i]``; entering a lambda
# extends the environment ``env + (v_d,)`` with the new binder thunk. Sharing of computation is preserved:
# a binder's argument thunk is created once at the application site and threaded in the environment, so
# all uses force one cell; two textually separate occurrences of the same sub-term are distinct redexes
# in call-by-need and are correctly recomputed (each occurrence calls the factory, making its own cell).
#
# Forcing a thunk is calling it. The factory / cell / thunk / (for a lambda) inner function of a node are
# named PATH-FREE by ``name_gensym_field(role, depth, quoted)``: the recursion is keyed only on
# ``(depth, quoted)`` so the interpreter TABLES it, the same (role, depth, sub-term) is one interned node,
# and the decoder assigns it one consistent ``vg_<n>``. The factories are wrapped in
# ``def _program(): <factories>; return mk_<root>(())`` and ``program = _program()`` binds it.

# Kind tag per emitted name: the top-level factory, the memo cell, the thunk, and (for a lambda) the
# inner function.
_KIND_FACTORY: Builder = church(0)
_KIND_THUNK: Builder = church(1)
_KIND_CELL: Builder = church(2)
_KIND_FUNCTION: Builder = church(3)

_PROGRAM_DEF_CODES: Builder = char_codes("_program")
_PROGRAM_BIND_CODES: Builder = char_codes("program")
_ENV_CODES: Builder = char_codes("env")
_ENV_NAME_FIELD: Builder = field_str(_ENV_CODES)
_ENV: Builder = ex_name(_ENV_NAME_FIELD)
# The lambda's inner function takes the argument thunk under one fixed name (each inner function is its
# own factory scope, so a fixed name never collides); it is immediately prepended to the environment.
_ARG_NAME_FIELD: Builder = field_str(char_codes("a"))
_ARG: Builder = ex_name(_ARG_NAME_FIELD)


# The recursion: self quoted -> (factory-defs difference-list, value function). The value is a FUNCTION
# from an environment EXPRESSION to the occurrence value ``mk_<node>(<environment>)``, so a parent can
# supply the right environment (``env`` inside a factory, or ``(a,) + env`` inside a lambda's body). It is
# keyed only by ``quoted`` -- DEPTH-FREE -- so the interpreter TABLES it on the sub-term alone: a sub-term
# shared across DIFFERENT binder depths compiles ONCE (binders are read positionally from the environment,
# ``env[index]``, so the compiled code never mentions the depth). This is what keeps compiling COMPILE
# tractable: its combinators recur at many depths, and a depth-keyed recursion recompiled each once per
# depth. The factory defs accumulate as a DIFFERENCE LIST (``rest -> my defs ++ rest``): combining two
# children is O(1) composition, not an O(length) append (eager append of whole def lists is quadratic).
# The accumulated list still carries the per-occurrence duplicates; the serializer drops the byte-identical
# copies (each factory is self-contained, so this is safe).
_CODEGEN_NEED_REC: Builder = app(Y, lam(lambda self_recursion: lam(
    lambda quoted: ap(
        quoted,
        # QVar index: the value reads the binder thunk from the environment at position ``index`` (the
        # environment is innermost-first, so the de Bruijn index IS the tuple index); no factory.
        lam(lambda index: pair(
            lam(lambda rest: rest),
            lam(lambda environment: py_subscript(environment, py_constant_int(index))),
        )),
        # QLam body: the thunk forces to an inner function ``def <func>(a): return <body value>``, where
        # the body is compiled in the EXTENDED environment ``(a,) + env`` (the new binder is innermost).
        lam(lambda body: let(
            ap(self_recursion, body),
            lambda compiled_body: pair(
                lam(lambda rest: cons(
                    lifted_factory(
                        name_gensym_field(_KIND_FACTORY, quoted),
                        one(_ENV_NAME_FIELD),
                        name_gensym_field(_KIND_CELL, quoted),
                        name_gensym_field(_KIND_THUNK, quoted),
                        two(
                            stmt(st_func_def(
                                name_gensym_field(_KIND_FUNCTION, quoted),
                                one(_ARG_NAME_FIELD),
                                one(stmt(st_return(ap(
                                    pair_second(compiled_body),
                                    py_add(py_tuple(one_node(_ARG)), _ENV),
                                )))),
                            )),
                            stmt(st_assign(
                                name_gensym_field(_KIND_CELL, quoted),
                                ex_name(name_gensym_field(_KIND_FUNCTION, quoted)),
                            )),
                        ),
                    ),
                    ap(pair_first(compiled_body), rest),
                )),
                lam(lambda environment: lifted_call(
                    name_gensym_field(_KIND_FACTORY, quoted), environment)),
            ),
        )),
        # QApp f a: the thunk forces ``force(<f value>)(<a value>)`` -- apply the function to the argument
        # thunk, then force the returned body thunk so the cell holds a value, not a thunk. Both children
        # are compiled in the SAME environment ``env``.
        lam(lambda function: lam(lambda argument: let(
            ap(self_recursion, function),
            lambda compiled_function: let(
                ap(self_recursion, argument),
                lambda compiled_argument: pair(
                    lam(lambda rest: cons(
                        lifted_factory(
                            name_gensym_field(_KIND_FACTORY, quoted),
                            one(_ENV_NAME_FIELD),
                            name_gensym_field(_KIND_CELL, quoted),
                            name_gensym_field(_KIND_THUNK, quoted),
                            one(stmt(st_assign(
                                name_gensym_field(_KIND_CELL, quoted),
                                ex_force(ex_app(
                                    ex_force(ap(pair_second(compiled_function), _ENV)),
                                    ap(pair_second(compiled_argument), _ENV),
                                )),
                            ))),
                        ),
                        ap(pair_first(compiled_function), ap(pair_first(compiled_argument), rest)),
                    )),
                    lam(lambda environment: lifted_call(
                        name_gensym_field(_KIND_FACTORY, quoted), environment)),
                ),
            ),
        ))),
    ),
)))


# CODEGEN_NEED wraps the root's factories in def _program(): <factories>; return mk_root(()), then
# program = _program(), all as a generic Scott ``ast.Module``. The root value applies the root's value
# function to the EMPTY environment ``()``. The factory list still carries the per-occurrence duplicates;
# ``_specialize`` drops them after decoding (each duplicate is byte-identical because the factories are
# lambda-lifted and self-contained).
CODEGEN_NEED: Builder = lam(lambda quoted: let(
    app(_CODEGEN_NEED_REC, quoted),
    lambda root: py_module(two(
        stmt(st_func_def(
            field_str(_PROGRAM_DEF_CODES),
            SCOTT_NIL,
            # pair_first(root) is the root's difference-list builder; apply it to the [return value] tail.
            ap(pair_first(root), one(stmt(st_return(ap(pair_second(root), py_tuple(SCOTT_NIL)))))),
        )),
        stmt(st_assign(
            field_str(_PROGRAM_BIND_CODES),
            ex_force(ex_name(field_str(_PROGRAM_DEF_CODES))),
        )),
    )),
))
