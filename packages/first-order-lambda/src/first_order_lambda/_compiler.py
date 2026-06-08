"""A lambda-calculus to Python compiler written in the lambda-calculus.

The source is a quoted lambda term, a Scott value over ``QVar i`` / ``QLam body`` / ``QApp f a`` (de
Bruijn). ``COMPILE`` is a pure lambda term that, GIVEN a compilation option, maps the quoted source to
a quoted Python expression, a Scott value over ``PyVar level`` / ``PyLam level body`` / ``PyApp f a``
/ ``PyForce e`` / ``PyThunk e``. The option decides the target, in the lambda term itself: under the
call-by-value option an application is a strict call and a variable is a bare name; under the
call-by-name option a variable is forced and an argument is thunked (``force``/``Thunk``), matching
the interpreter's weak-head reduction. So the target-specific codegen lives in the lambda term; Python
only quotes the input, supplies the option, runs the interpreter, and decodes the resulting Scott
Python expression with a single generic decoder.

The interpret target is not a compiled target. It means interpret: re-submit the term to the
interpreter, whose interning gives the genuine cross-graph tabling fold. (The old compiled fixpoint
thunk, a ``fixpoint_cached_property`` per thunk, had no cross-graph tabling and is removed.)
"""

from __future__ import annotations

import ast
import sys
from contextlib import contextmanager
from enum import Enum, auto
from typing import Iterator

from first_order_lambda import _pybuild
from first_order_lambda._ast import App, Lam, Node, Var, make_app, make_lam, make_native, make_var
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import FALSE, PLUS, PRED, SCOTT_NIL, SUCC, TRUE, church, cons, map_list
from first_order_lambda._pyast import _church_to_int, decode

# The strict (call-by-value) fixpoint combinator Z = lambda f. (lambda x. f (lambda v. x x v)) (...).
# Unlike Y it is eta-expanded under the recursive call, so the compiled Python (a strict language)
# terminates where the compiled Y would diverge; in our weak-head interpreter it is an ordinary
# fixpoint just like Y.
Z: Builder = lam(lambda f: app(
    lam(lambda x: app(f, lam(lambda v: app(app(x, x), v)))),
    lam(lambda x: app(f, lam(lambda v: app(app(x, x), v)))),
))


def _scott(arity: int, tag: int, fields: "list[Builder]") -> Builder:
    """A Scott constructor over ``arity`` cases: select the ``tag``-th handler and apply the fields."""
    def collect(handlers: "list[Builder]") -> Builder:
        if len(handlers) == arity:
            applied = handlers[tag]
            for field in fields:
                applied = app(applied, field)
            return applied
        return lam(lambda handler: collect(handlers + [handler]))

    return collect([])


# Quoted source: three constructors (QVar/QLam/QApp).
def q_var(index: Builder) -> Builder:
    return _scott(3, 0, [index])


def q_lam(body: Builder) -> Builder:
    return _scott(3, 1, [body])


def q_app(function: Builder, argument: Builder) -> Builder:
    return _scott(3, 2, [function, argument])


# The compiler emits the GENERIC _pyast Scott encoding of a real Python ast (built with the lambda-term
# smart constructors in _pybuild), decoded by the generic _pyast.decode. A variable at de Bruijn level
# k is named ``v`` followed by k copies of ``x`` (unique, valid, built by Church iteration over the
# level); the call-by-name target wraps a variable/function in ``force(...)`` and an argument in
# ``Thunk(lambda: ...)``.

# sub a b = a - b, by applying PRED to a, b times.
_SUB: Builder = lam(lambda a: lam(lambda b: app(app(b, PRED), a)))

# A level (Church numeral) to its identifier char codes: ``v`` :: (``x`` * level).
_PREPEND_X: Builder = lam(lambda rest: cons(church(120), rest))


def _level_codes(level: Builder) -> Builder:
    return cons(church(118), app(app(level, _PREPEND_X), SCOTT_NIL))


def _single_arg(expr: Builder) -> Builder:
    """The argument list of a Call with one positional argument (a Scott list of one node field)."""
    return cons(_pybuild.field_node(expr), SCOTT_NIL)


_FORCE_NAME: Builder = _pybuild.py_name(_pybuild.char_codes("force"), _pybuild.py_load())
_THUNK_NAME: Builder = _pybuild.py_name(_pybuild.char_codes("Thunk"), _pybuild.py_load())

# Target wrappers, selected by the option (a Church boolean ``thunked``): the call-by-name target wraps
# a variable and a function in ``force(...)`` and an argument in ``Thunk(lambda: ...)``; call-by-value
# wraps with identity.
_FORCE_WRAP: Builder = lam(lambda expr: _pybuild.py_call(_FORCE_NAME, _single_arg(expr)))
_THUNK_WRAP: Builder = lam(lambda expr: _pybuild.py_call(_THUNK_NAME, _single_arg(_pybuild.py_lambda0(expr))))
_IDENTITY_WRAP: Builder = lam(lambda expr: expr)


def _select_wrap(thunked: Builder, lazy_wrap: Builder) -> Builder:
    # thunked is a Church boolean: it picks lazy_wrap when lazy (TRUE), identity when eager (FALSE).
    return app(app(thunked, lazy_wrap), _IDENTITY_WRAP)


# COMPILE = lambda thunked. Z (lambda self. lambda d. lambda q.
#   q (lambda i. wrapVar (Name "v<d-1-i>"))                                  -- QVar i
#     (lambda b. Lambda "v<d>" (self (succ d) b))                           -- QLam b
#     (lambda f. lambda a. Call (wrapFun (self d f)) [wrapArg (self d a)]))  -- QApp f a
# wrapVar = wrapFun = (thunked ? force : id); wrapArg = (thunked ? Thunk(lambda: .) : id).
COMPILE: Builder = lam(lambda thunked: app(
    Z,
    lam(lambda self_recursion: lam(lambda depth: lam(lambda quoted: app(app(app(
        quoted,
        lam(lambda index: app(
            _select_wrap(thunked, _FORCE_WRAP),
            _pybuild.py_name(_level_codes(app(app(_SUB, depth), app(SUCC, index))), _pybuild.py_load()),
        )),
        ),
        lam(lambda body: _pybuild.py_lambda(
            _level_codes(depth), app(app(self_recursion, app(SUCC, depth)), body),
        )),
        ),
        lam(lambda function: lam(lambda argument: _pybuild.py_call(
            app(_select_wrap(thunked, _FORCE_WRAP), app(app(self_recursion, depth), function)),
            _single_arg(app(_select_wrap(thunked, _THUNK_WRAP), app(app(self_recursion, depth), argument))),
        ))),
    )))),
))


def quote(node: Node) -> Builder:
    """Reflect an interpreter lambda ``Node`` into a quoted-lambda Scott source term."""
    match node:
        case Var(index=index):
            return q_var(church(index))
        case Lam(body=body):
            return q_lam(quote(body))
        case App(function=function, argument=argument):
            return q_app(quote(function), quote(argument))
        case _:
            raise ValueError(f"cannot quote {node!r}")


class Runtime(Enum):
    CALL_BY_VALUE = auto()  # strict: an argument is evaluated to a value before the call
    CALL_BY_NAME = auto()  # an argument is a thunk recomputed on each force (no sharing)
    CALL_BY_NEED = auto()  # call-by-name plus memoisation: the thunk computes once and shares
    INTERPRET = auto()  # not a compiled target: re-submit the term to the interpreter


def _option(runtime: Runtime) -> Builder:
    """The Scott compilation option for a compiled target: a Church boolean ``thunked``."""
    if runtime is Runtime.CALL_BY_VALUE:
        return FALSE
    if runtime is Runtime.CALL_BY_NAME:
        return TRUE
    if runtime is Runtime.CALL_BY_NEED:
        raise NotImplementedError("call-by-need codegen (explicit memoising thunks) is not built yet")
    raise ValueError("the interpret target is not compiled; compile call-by-value or call-by-name")


def compile_quoted(option: Builder, quoted: Builder) -> Node:
    """Run ``COMPILE`` (at the given option) on a quoted source term, returning the Scott Python expr."""
    return build(app(app(app(COMPILE, option), church(0)), quoted))


# --- runtime support for the compiled call-by-name target ---------------------------------------
# The call-by-name target's emitted Python refers to the free names ``force`` and ``Thunk``. An
# argument is a thunk ``Thunk(lambda: a)`` recomputed on each ``force``, matching the interpreter's
# weak-head reduction so every normalizing term computes its value. (The call-by-value target is
# strict and self-contained; the interpret target is the interpreter, not a compiled runtime.)


class _Thunk:
    """A delayed computation; ``force`` evaluates it."""

    __slots__ = ("_fn", "__dict__")

    def __init__(self, fn) -> None:
        self._fn = fn


class _LazyThunk(_Thunk):
    @property
    def value(self):
        return self._fn()  # call-by-name: recompute on every force


def force(value):
    return value.value if isinstance(value, _Thunk) else value


def runtime_globals(runtime: Runtime) -> dict:
    """The evaluation globals for a compiled program under the given runtime.

    Call-by-value source is self-contained; call-by-name source needs ``force`` and the
    recompute-on-force ``Thunk``.
    """
    if runtime is Runtime.CALL_BY_VALUE:
        return {}
    if runtime is Runtime.CALL_BY_NAME:
        return {"force": force, "Thunk": _LazyThunk}
    if runtime is Runtime.CALL_BY_NEED:
        return call_by_need_globals()
    raise ValueError("the interpret target is interpreted; it has no compiled runtime globals")


# Building and decoding the generic Scott ast recurses about as deep as the term, and the generic
# encoding's n-ary constructors are deeper than the old bespoke ones, so give the interpreter stack
# headroom above Python's default (the recursion is finite; raising the limit, restored after, is the
# fix, not a workaround). This is genuine finite recursion, unlike the tokenizer's paren-nesting cap.
_COMPILE_RECURSION_LIMIT = 16_000


@contextmanager
def _recursion_headroom() -> "Iterator[None]":
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(max(previous, _COMPILE_RECURSION_LIMIT))
    try:
        yield
    finally:
        sys.setrecursionlimit(previous)


def compile_to_source(node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile an interpreter lambda term to Python source for the given compiled target.

    Call-by-value yields a strict expression; call-by-name yields the expression with the lambda
    term's ``force``/``Thunk`` wrapping; call-by-need yields a memoising-thunk module. Every target is
    built as the generic Scott ast and decoded by ``_pyast.decode``. The interpret target is not here.
    """
    with _recursion_headroom():
        if runtime is Runtime.CALL_BY_NEED:
            return _compile_need_source(node)
        compiled = compile_quoted(_option(runtime), quote(node))
        return ast.unparse(ast.fix_missing_locations(decode(compiled)))


# --- the interpret target: emit Python that re-submits the term to the interpreter ---------------
# A term the analysis does not certify for a compiled target keeps the interpreter. Its compiled
# Python is an ``interpret(...)`` call whose argument reconstructs the term as an interpreter ``Node``
# with ``make_var`` / ``make_lam`` / ``make_app`` (the interning constructors), so the emitted source
# is self-contained text given the four names in ``interpret_globals``. ``interpret`` hands the node
# to the interpreter; the node is the value, normalized lazily when the result is observed. This is
# the head of a specialized program: a by-value-certified subgraph compiles inline, the rest reads
# ``interpret(...)``.


def _island_call(node: Node, kind: str, arity: int) -> ast.expr:
    """The Python that splices ``node`` as a compiled island of the given ``kind``.

    ``identity`` needs no compiled body (a closed ``a -> a`` term is the identity); ``church_data`` and
    ``church_function`` embed the island compiled to call-by-value, which their runtimes drive.
    """
    if kind == "identity":
        return ast.Call(func=ast.Name(id="identity_island", ctx=ast.Load()), args=[], keywords=[])
    compiled = ast.parse(compile_to_source(node, Runtime.CALL_BY_VALUE), mode="eval").body
    if kind == "church_data":
        return ast.Call(func=ast.Name(id="church_island", ctx=ast.Load()), args=[compiled], keywords=[])
    if kind == "church_function":
        return ast.Call(
            func=ast.Name(id="church_function_island", ctx=ast.Load()),
            args=[compiled, ast.Constant(value=arity)], keywords=[],
        )
    raise ValueError(f"unknown island kind {kind!r}")


def _node_to_ast(node: Node, islands: "dict[int, tuple[str, int]]") -> ast.expr:
    """Reconstruct ``node`` as Python that rebuilds the interpreter ``Node`` with ``make_*``.

    A node whose identity is in ``islands`` is a certified by-value island: rather than reconstructing
    its subtree, splice it as a compiled island (``_island_call``) the interpreter drives in place of
    interpreting the subtree, reifying through the FFI scoped to the island's type.
    """
    if id(node) in islands:
        kind, arity = islands[id(node)]
        return _island_call(node, kind, arity)
    match node:
        case Var(index=index):
            return ast.Call(
                func=ast.Name(id="make_var", ctx=ast.Load()),
                args=[ast.Constant(value=index)], keywords=[],
            )
        case Lam(body=body):
            return ast.Call(
                func=ast.Name(id="make_lam", ctx=ast.Load()), args=[_node_to_ast(body, islands)],
                keywords=[],
            )
        case App(function=function, argument=argument):
            return ast.Call(
                func=ast.Name(id="make_app", ctx=ast.Load()),
                args=[_node_to_ast(function, islands), _node_to_ast(argument, islands)], keywords=[],
            )
        case _:
            raise ValueError(f"cannot reconstruct {node!r}")


def interpret(node: Node) -> Node:
    """The interpret boundary: a reconstructed term handed back to the interpreter.

    The node is the value; the interpreter computes its weak head normal form lazily when the result
    is observed (decoded, rendered, or applied at the node level). This is the runtime hook a compiled
    by-value island is spliced around in a specialized program.
    """
    return node


def _host_church(n: int):
    """A host Church numeral for ``n``: ``lambda s: lambda z: s^n z``."""
    def successor(s):
        def zero(z):
            result = z
            for _ in range(n):
                result = s(result)
            return result
        return zero
    return successor


def _decode_host_church(value) -> int:
    return value(lambda predecessor: predecessor + 1)(0)


def identity_island() -> Node:
    """The island for a closed ``a -> a`` term: by parametricity it is the identity, so a passthrough
    ``Native`` returning its argument node unchanged, sound on any argument encoding."""
    return make_native(lambda argument: argument, 1)


def church_island(compiled_value) -> Node:
    """A church-numeral DATA island (a closed church-producing term, no arguments).

    The FFI ``Native`` (arity 0) evaluates the compiled call-by-value code, decodes the Church numeral,
    and reifies it as a Church-numeral node, so the island runs compiled while the interpreter folds
    around it. Faithfulness is convergence to the same value, not structural identity.
    """
    return make_native(lambda: build(church(_decode_host_church(compiled_value))), 0)


def church_function_island(compiled_value, arity: int) -> Node:
    """A church-function island: a closed term of type ``church -> ... -> church`` (``arity`` arrows).

    The ``Native`` collects ``arity`` Church-numeral argument nodes, decodes each to an integer and
    rebuilds a host Church numeral, applies the compiled call-by-value function, and reifies the
    Church-numeral result. Sound where the island is applied to Church numerals, which is its typing.
    """
    def run(*argument_nodes: Node) -> Node:
        result = compiled_value
        for argument_node in argument_nodes:
            result = result(_host_church(_church_to_int(argument_node)))
        return build(church(_decode_host_church(result)))

    return make_native(run, arity)


def interpret_globals() -> dict:
    """The evaluation globals for interpret-headed source: node constructors, ``interpret``, islands."""
    return {
        "make_var": make_var, "make_lam": make_lam, "make_app": make_app, "interpret": interpret,
        "identity_island": identity_island, "church_island": church_island,
        "church_function_island": church_function_island,
    }


def compile_interpreted(node: Node, islands: "dict[int, tuple[str, int]] | None" = None) -> str:
    """Compile ``node`` to interpret-headed Python: ``interpret(<node reconstructed with make_*>)``.

    Sub-nodes whose identity is in ``islands`` (mapping identity to a ``(kind, arity)`` classification)
    are spliced as compiled islands rather than reconstructed, so they run compiled inside the
    interpreted skeleton.
    """
    call = ast.Call(
        func=ast.Name(id="interpret", ctx=ast.Load()),
        args=[_node_to_ast(node, islands if islands is not None else {})], keywords=[],
    )
    return ast.unparse(ast.fix_missing_locations(call))


def compile_with_interpreted(compiler_node: Node, node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile ``node`` with an interpret-headed compiler, a ``COMPILE`` ``Node`` run by the interpreter.

    ``compiler_node`` is what ``compile_interpreted(build(COMPILE))`` evaluates to: the compiler itself,
    handed back to the interpreter. The interpreter applies it to the option, depth ``0``, and the
    quoted program, and the resulting generic Scott Python AST is decoded by the same generic
    ``_pyast.decode`` the in-process compiler uses. So the self-hosted compiler, compiled to
    interpret-headed Python, compiles any program to the same source as ``compile_to_source``: the
    bootstrap through the interpret target.
    """
    with _recursion_headroom():
        applied = make_app(
            make_app(make_app(compiler_node, build(_option(runtime))), build(church(0))),
            build(quote(node)),
        )
        return ast.unparse(ast.fix_missing_locations(decode(applied)))


# --- call-by-need: explicit memoising thunks, emitted entirely by the COMPILE_NEED lambda term ---
# Call-by-need adds sharing to call-by-name: a thunk computes once and caches. The cache and its
# update need statements, so the target is statement-based, and the WHOLE structure (the def, the
# nonlocal, the sentinel guard, the assignment, the return, the module wrapper) is emitted by the
# COMPILE_NEED lambda term as a Scott-encoded Python AST. Python only decodes that AST 1:1; it
# assembles nothing. Every sub-term compiles to a memoising thunk of the shape the design fixed:
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
# decoded to an underscore-joined name like ``v_0_2_1`` that is unique by construction. A binder's
# symbol is threaded down in an environment so a variable looks up its binder's name by de Bruijn
# index. The program is wrapped in ``def _program(): ...; return <root thunk>`` so the ``nonlocal``
# cells have an enclosing function scope, and ``program = _program()`` binds it.

# Path segments: a branch index per descent (function/argument/lambda-body) and a kind tag per role.
_BRANCH_FUNCTION: Builder = church(0)
_BRANCH_ARGUMENT: Builder = church(1)
_BRANCH_BODY: Builder = church(2)
_KIND_THUNK: Builder = church(0)
_KIND_CELL: Builder = church(1)
_KIND_FUNCTION: Builder = church(2)
_KIND_VARIABLE: Builder = church(3)


def _let(value: Builder, body: "object") -> Builder:
    """Bind ``value`` for ``body`` (a Python ``lambda`` over the bound Builder)."""
    return app(lam(body), value)


def _one(element: Builder) -> Builder:
    return cons(element, SCOTT_NIL)


def _two(first: Builder, second: Builder) -> Builder:
    return cons(first, cons(second, SCOTT_NIL))


# append xs ys = xs (lambda h. lambda t. cons h (self t ys)) ys, by Scott-list elimination.
_APPEND: Builder = app(Z, lam(lambda self_recursion: lam(lambda xs: lam(lambda ys: app(
    app(xs, lam(lambda head: lam(lambda tail: cons(head, app(app(self_recursion, tail), ys))))),
    ys,
)))))


def _append(xs: Builder, ys: Builder) -> Builder:
    return app(app(_APPEND, xs), ys)


# tail/head by Scott-list elimination; nth drops ``index`` heads (Church iteration) then takes head.
_TAIL: Builder = lam(lambda lst: app(app(lst, lam(lambda head: lam(lambda tail: tail))), SCOTT_NIL))
_HEAD: Builder = lam(lambda lst: app(app(lst, lam(lambda head: lam(lambda tail: head))), SCOTT_NIL))
_NTH: Builder = lam(lambda index: lam(lambda env: app(_HEAD, app(app(index, _TAIL), env))))


# A compiled (sub)term is a Scott pair of its setup statements and its value expression.
def _need_pair(setup: Builder, value: Builder) -> Builder:
    return lam(lambda selector: app(app(selector, setup), value))


def _fst(pair: Builder) -> Builder:
    return app(pair, TRUE)


def _snd(pair: Builder) -> Builder:
    return app(pair, FALSE)


_SENTINEL_NAME = "CALL_BY_NEED_SENTINEL"

# Identifiers are built by the lambda term as char codes for the generic _pyast string field. A symbol
# is the AST path (Church-numeral segments, each a single digit 0-3) rendered "v_<seg>_<seg>..."; the
# two wrapper names are fixed char-code literals.
_RENDER_PATH: Builder = app(Z, lam(lambda render: lam(lambda path: app(app(
    path,
    lam(lambda segment: lam(lambda rest: cons(
        church(95), cons(app(app(PLUS, church(48)), segment), app(render, rest)),
    ))),
    ),
    SCOTT_NIL,
))))


def _sym_path_codes(path: Builder) -> Builder:
    return cons(church(118), app(_RENDER_PATH, path))  # 'v' :: ('_' :: digit :: ...)


def _name_symbol_codes(kind: Builder, path: Builder) -> Builder:
    """The char codes naming the ``kind`` identifier of the node at ``path`` (kind tag is the path head)."""
    return _sym_path_codes(cons(kind, path))


_PROGRAM_DEF_CODES: Builder = _pybuild.char_codes("_program")
_PROGRAM_BIND_CODES: Builder = _pybuild.char_codes("program")
_SENTINEL_CODES: Builder = _pybuild.char_codes(_SENTINEL_NAME)


# Expressions, built as the generic Scott Python AST via the _pybuild smart constructors.
def _ex_name(codes: Builder) -> Builder:
    return _pybuild.py_name(codes, _pybuild.py_load())


_EX_SENTINEL: Builder = _ex_name(_SENTINEL_CODES)


def _ex_force(expr: Builder) -> Builder:
    return _pybuild.py_call(expr, SCOTT_NIL)  # expr()


def _ex_app(function: Builder, argument: Builder) -> Builder:
    return _pybuild.py_call(function, _single_arg(argument))  # function(argument)


def _ex_is(left: Builder, right: Builder) -> Builder:
    return _pybuild.py_compare_is(left, right)  # left is right


def _stmt(node: Builder) -> Builder:
    """Wrap a statement node as a field so it can sit in a Scott list of statements."""
    return _pybuild.field_node(node)


# Statements, built as the generic Scott Python AST. A body argument is a Scott list of statement
# fields (``_stmt`` of each); a parameter/name list is a Scott list of char-code lists.
def _st_func_def(name_codes: Builder, parameter_codes: Builder, body_fields: Builder) -> Builder:
    arguments = _pybuild.py_arguments(
        map_list(lam(lambda code: _pybuild.field_node(_pybuild.py_arg(code))), parameter_codes),
    )
    return _pybuild.py_function_def(name_codes, arguments, body_fields)


def _st_nonlocal(name_codes_list: Builder) -> Builder:
    return _pybuild.py_nonlocal(map_list(lam(lambda code: _pybuild.field_str(code)), name_codes_list))


def _st_if(test: Builder, body_fields: Builder) -> Builder:
    return _pybuild.py_if(test, body_fields)


def _st_assign(target_codes: Builder, value: Builder) -> Builder:
    return _pybuild.py_assign(_pybuild.py_name(target_codes, _pybuild.py_store()), value)


def _st_return(value: Builder) -> Builder:
    return _pybuild.py_return(value)


def _thunk_scaffold(cell_codes: Builder, thunk_codes: Builder, compute_fields: Builder) -> Builder:
    """The two setup statement fields introducing a memoising thunk: the cell init and the thunk def."""
    body = cons(
        _stmt(_st_nonlocal(_one(cell_codes))),
        cons(
            _stmt(_st_if(_ex_is(_ex_name(cell_codes), _EX_SENTINEL), compute_fields)),
            _one(_stmt(_st_return(_ex_name(cell_codes)))),
        ),
    )
    return _two(
        _stmt(_st_assign(cell_codes, _EX_SENTINEL)),
        _stmt(_st_func_def(thunk_codes, SCOTT_NIL, body)),
    )


# The recursion: self path env quoted -> (setup statements, value expression). ``path`` is the AST
# address (Church segments, innermost first); ``env`` is the list of in-scope binder symbols.
_COMPILE_NEED_REC: Builder = app(Z, lam(lambda self_recursion: lam(lambda path: lam(lambda env: lam(
    lambda quoted: app(app(app(
        quoted,
        # QVar index: the variable is its binder's thunk, looked up by de Bruijn index; no setup.
        lam(lambda index: _need_pair(SCOTT_NIL, _ex_name(app(app(_NTH, index), env)))),
        ),
        # QLam body: the value is an inner function; wrap it in a memoising thunk.
        lam(lambda body: _let(
            _name_symbol_codes(_KIND_VARIABLE, path),
            lambda parameter: _let(
                app(app(app(self_recursion, cons(_BRANCH_BODY, path)), cons(parameter, env)), body),
                lambda compiled_body: _need_pair(
                    _thunk_scaffold(
                        _name_symbol_codes(_KIND_CELL, path),
                        _name_symbol_codes(_KIND_THUNK, path),
                        _two(
                            _stmt(_st_func_def(
                                _name_symbol_codes(_KIND_FUNCTION, path),
                                _one(parameter),
                                _append(_fst(compiled_body), _one(_stmt(_st_return(_snd(compiled_body))))),
                            )),
                            _stmt(_st_assign(
                                _name_symbol_codes(_KIND_CELL, path),
                                _ex_name(_name_symbol_codes(_KIND_FUNCTION, path)),
                            )),
                        ),
                    ),
                    _ex_name(_name_symbol_codes(_KIND_THUNK, path)),
                ),
            ),
        )),
        ),
        # QApp f a: force the function and apply the argument thunk; the result is a memoising thunk.
        lam(lambda function: lam(lambda argument: _let(
            app(app(app(self_recursion, cons(_BRANCH_FUNCTION, path)), env), function),
            lambda compiled_function: _let(
                app(app(app(self_recursion, cons(_BRANCH_ARGUMENT, path)), env), argument),
                lambda compiled_argument: _need_pair(
                    _thunk_scaffold(
                        _name_symbol_codes(_KIND_CELL, path),
                        _name_symbol_codes(_KIND_THUNK, path),
                        _append(
                            _fst(compiled_function),
                            _append(
                                _fst(compiled_argument),
                                _one(_stmt(_st_assign(
                                    _name_symbol_codes(_KIND_CELL, path),
                                    # Force to WHNF: applying the function returns the body thunk, which
                                    # must itself be forced so this cell holds a value, not a thunk.
                                    _ex_force(_ex_app(
                                        _ex_force(_snd(compiled_function)), _snd(compiled_argument),
                                    )),
                                ))),
                            ),
                        ),
                    ),
                    _ex_name(_name_symbol_codes(_KIND_THUNK, path)),
                ),
            ),
        ))),
    ))))))


# COMPILE_NEED wraps the root's (statements, value) in def _program(): ...; return value, then
# program = _program(), all as a generic Scott ``ast.Module``.
COMPILE_NEED: Builder = lam(lambda quoted: _let(
    app(app(app(_COMPILE_NEED_REC, SCOTT_NIL), SCOTT_NIL), quoted),
    lambda root: _pybuild.py_module(_two(
        _stmt(_st_func_def(
            _PROGRAM_DEF_CODES, SCOTT_NIL, _append(_fst(root), _one(_stmt(_st_return(_snd(root))))),
        )),
        _stmt(_st_assign(_PROGRAM_BIND_CODES, _ex_force(_ex_name(_PROGRAM_DEF_CODES)))),
    )),
))


class _CallByNeedSentinel:
    """The unforced marker stored in a memo cell before its thunk computes."""

    def __repr__(self) -> str:
        return _SENTINEL_NAME


def call_by_need_globals() -> dict:
    """The evaluation globals for a call-by-need program: just the unforced-cell sentinel.

    Forcing is calling a thunk, so there is no ``force`` helper; the emitted module is self-contained
    apart from the sentinel its memo cells compare against.
    """
    return {_SENTINEL_NAME: _CallByNeedSentinel()}


def _compile_need_source(node: Node) -> str:
    """Compile a term to the call-by-need module source (explicit memoising thunks).

    COMPILE_NEED emits the generic Scott ``ast.Module`` directly, decoded by the generic ``_pyast.decode``.
    """
    module = build(app(COMPILE_NEED, quote(node)))
    return ast.unparse(ast.fix_missing_locations(decode(module)))


# --- bootstrap: the self-compiled compiler, run through the interpret target --------------------
# COMPILE compiled in specialized mode is interpret-headed (COMPILE is untypable: its Z fixpoint
# self-applies), so the self-hosted compiler is the COMPILE node handed back to the interpreter.
# ``compiled_compiler`` evaluates that interpret-headed source to the node; ``compile_with_interpreted``
# runs it as a compiler, reifying the Scott Python-AST result through ``_decode_pyast``, the same
# boundary the in-process compiler uses. So the compiler compiled by itself, through interpret, is a
# working compiler agreeing with ``compile_to_source``.


def compiled_compiler() -> Node:
    """The self-hosted compiler as an interpreter ``Node``: COMPILE handed back to the interpreter.

    COMPILE is untypable, so the interpret target is the COMPILE node itself; ``compile_with_interpreted``
    runs it as a compiler. (The committed standalone source artifact, ``_generated_compiler.py``, is the
    business of the bootstrap stage; the generic-encoding COMPILE's full reconstruction exceeds Python's
    parser limit, so that artifact is reworked there. In process, the node IS the self-compiled compiler.)
    """
    return build(COMPILE)
