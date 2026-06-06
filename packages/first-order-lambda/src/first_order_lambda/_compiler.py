"""A lambda-calculus to Python compiler written in the lambda-calculus.

The source is a quoted lambda term, a Scott value over three constructors ``QVar i`` / ``QLam body``
/ ``QApp f a`` (de Bruijn). ``COMPILE`` is a pure lambda term that maps it to a quoted Python
expression, a Scott value over ``PyVar level`` / ``PyLam level body`` / ``PyApp f a``: an
abstraction becomes a Python ``lambda``, an application a call, and a variable a name. The compiler
threads the binder depth so that a de Bruijn index ``i`` at depth ``d`` becomes the level
``d - 1 - i`` (computed with Church subtraction), giving stable parameter names ``v{level}``. A
meta-level ``quote`` turns an interpreter ``Node`` into the quoted source, and a meta-level decoder
turns the compiled Scott value, run in the interpreter, into a real Python ``ast`` expression.
"""

from __future__ import annotations

import ast
from enum import Enum, auto

from fixpoints._core import fixpoint_cached_property

from first_order_lambda._ast import App, Lam, Node, Var
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import PRED, SUCC, church
from first_order_lambda._pyast import _church_to_int, _extract

_PY_BASE = 5_000_000

# The strict (call-by-value) fixpoint combinator Z = lambda f. (lambda x. f (lambda v. x x v)) (...).
# Unlike Y it is eta-expanded under the recursive call, so the compiled Python (a strict language)
# terminates where the compiled Y would diverge; in our weak-head interpreter it is an ordinary
# fixpoint just like Y.
Z: Builder = lam(lambda f: app(
    lam(lambda x: app(f, lam(lambda v: app(app(x, x), v)))),
    lam(lambda x: app(f, lam(lambda v: app(app(x, x), v)))),
))


def _scott3(tag: int, fields: "list[Builder]") -> Builder:
    def collect(handlers: "list[Builder]") -> Builder:
        if len(handlers) == 3:
            applied = handlers[tag]
            for field in fields:
                applied = app(applied, field)
            return applied
        return lam(lambda handler: collect(handlers + [handler]))

    return collect([])


def q_var(index: Builder) -> Builder:
    return _scott3(0, [index])


def q_lam(body: Builder) -> Builder:
    return _scott3(1, [body])


def q_app(function: Builder, argument: Builder) -> Builder:
    return _scott3(2, [function, argument])


def _py_var(level: Builder) -> Builder:
    return _scott3(0, [level])


def _py_lam(level: Builder, body: Builder) -> Builder:
    return _scott3(1, [level, body])


def _py_app(function: Builder, argument: Builder) -> Builder:
    return _scott3(2, [function, argument])


# sub a b = a - b, by applying PRED to a, b times.
_SUB: Builder = lam(lambda a: lam(lambda b: app(app(b, PRED), a)))

# COMPILE = Y (lambda self. lambda d. lambda q.
#   q (lambda i. PyVar (sub d (succ i)))            -- QVar i
#     (lambda b. PyLam d (self (succ d) b))         -- QLam b
#     (lambda f. lambda a. PyApp (self d f) (self d a)))  -- QApp f a
COMPILE: Builder = app(
    Z,
    lam(lambda self_recursion: lam(lambda depth: lam(lambda quoted: app(app(app(
        quoted,
        lam(lambda index: _py_var(app(app(_SUB, depth), app(SUCC, index)))),
        ),
        lam(lambda body: _py_lam(depth, app(app(self_recursion, app(SUCC, depth)), body))),
        ),
        lam(lambda function: lam(lambda argument: _py_app(
            app(app(self_recursion, depth), function),
            app(app(self_recursion, depth), argument),
        ))),
    )))),
)


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


def compile_quoted(quoted: Builder) -> Node:
    """Run ``COMPILE`` on a quoted source term, returning the compiled Scott Python expression."""
    return build(app(app(COMPILE, church(0)), quoted))


def _decode_pyexpr(node: Node) -> ast.expr:
    tag, fields = _extract(node, (1, 2, 2), _PY_BASE)  # PyVar/PyLam/PyApp
    match tag:
        case 0:  # PyVar level
            return ast.Name(id=f"v{_church_to_int(fields[0])}", ctx=ast.Load())
        case 1:  # PyLam level body
            name = f"v{_church_to_int(fields[0])}"
            return ast.Lambda(
                args=ast.arguments(
                    posonlyargs=[], args=[ast.arg(arg=name)], kwonlyargs=[],
                    kw_defaults=[], defaults=[],
                ),
                body=_decode_pyexpr(fields[1]),
            )
        case 2:  # PyApp function argument
            return ast.Call(
                func=_decode_pyexpr(fields[0]), args=[_decode_pyexpr(fields[1])], keywords=[],
            )
        case _:
            raise ValueError(f"unknown PyExpr tag {tag}")


# --- runtimes -----------------------------------------------------------------------------------
# Three target runtimes select how the compiled Python evaluates. EAGER is strict (call-by-value):
# an application f(a) evaluates a before the call, so a Church conditional's unselected branch is
# forced and a Y recursion diverges. LAZY and FIXPOINT share one thunk-based target: an argument is
# a thunk Thunk(lambda: a) and a variable reference forces it, so only the selected branch runs and
# a Y recursion over a normalizing term terminates, matching the interpreter's weak-head reduction.
# LAZY and FIXPOINT differ only in the thunk: LAZY recomputes on each force (call-by-name), while
# FIXPOINT memoises the value with fixpoint_cached_property, so a re-entrant (self-referential) force
# folds to BOTTOM rather than looping, the same least-fixpoint fold the interpreter performs.


class Runtime(Enum):
    EAGER = auto()
    LAZY = auto()
    FIXPOINT = auto()


class _Bottom:
    def __repr__(self) -> str:
        return "BOTTOM"


BOTTOM = _Bottom()


class _Thunk:
    """A delayed computation; ``force`` evaluates it."""

    __slots__ = ("_fn", "__dict__")

    def __init__(self, fn) -> None:
        self._fn = fn


class _LazyThunk(_Thunk):
    @property
    def value(self):
        return self._fn()  # call-by-name: recompute on every force


class _FixpointThunk(_Thunk):
    @fixpoint_cached_property(bottom=lambda: BOTTOM)
    def value(self):
        return self._fn()  # call-by-need: memoised, and a re-entrant force folds to BOTTOM


def force(value):
    return value.value if isinstance(value, _Thunk) else value


_THUNK_CLASS = {Runtime.LAZY: _LazyThunk, Runtime.FIXPOINT: _FixpointThunk}


def runtime_globals(runtime: Runtime) -> dict:
    """The evaluation globals for a compiled thunk-based program under the given runtime."""
    return {"force": force, "Thunk": _THUNK_CLASS[runtime]}


def _no_args() -> ast.arguments:
    return ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[])


def _decode_pyexpr_thunk(node: Node) -> ast.expr:
    # Shared target for LAZY and FIXPOINT: variables are forced, arguments are thunks.
    tag, fields = _extract(node, (1, 2, 2), _PY_BASE)
    match tag:
        case 0:  # PyVar level: force(v{level})
            name = f"v{_church_to_int(fields[0])}"
            return ast.Call(
                func=ast.Name(id="force", ctx=ast.Load()),
                args=[ast.Name(id=name, ctx=ast.Load())],
                keywords=[],
            )
        case 1:  # PyLam level body: lambda v{level}: body
            name = f"v{_church_to_int(fields[0])}"
            return ast.Lambda(
                args=ast.arguments(
                    posonlyargs=[], args=[ast.arg(arg=name)], kwonlyargs=[],
                    kw_defaults=[], defaults=[],
                ),
                body=_decode_pyexpr_thunk(fields[1]),
            )
        case 2:  # PyApp function argument: force(function)(Thunk(lambda: argument))
            return ast.Call(
                func=ast.Call(
                    func=ast.Name(id="force", ctx=ast.Load()),
                    args=[_decode_pyexpr_thunk(fields[0])],
                    keywords=[],
                ),
                args=[ast.Call(
                    func=ast.Name(id="Thunk", ctx=ast.Load()),
                    args=[ast.Lambda(args=_no_args(), body=_decode_pyexpr_thunk(fields[1]))],
                    keywords=[],
                )],
                keywords=[],
            )
        case _:
            raise ValueError(f"unknown PyExpr tag {tag}")


def compile_to_source(node: Node, runtime: Runtime = Runtime.EAGER) -> str:
    """Compile an interpreter lambda term to Python source for the given target runtime.

    EAGER yields a strict expression; LAZY and FIXPOINT yield the same thunk-based expression
    (referring to the free names ``force`` and ``Thunk``, supplied by ``runtime_globals``).
    """
    compiled = compile_quoted(quote(node))
    decode = _decode_pyexpr if runtime is Runtime.EAGER else _decode_pyexpr_thunk
    return ast.unparse(ast.fix_missing_locations(decode(compiled)))


# --- bootstrap: run the self-compiled compiler, as a Python function, on Python-encoded input ---

def _python_church(n: int):
    def successor(s):
        def zero(z):
            result = z
            for _ in range(n):
                result = s(result)
            return result
        return zero
    return successor


def _python_church_to_int(numeral) -> int:
    return numeral(lambda k: k + 1)(0)


def _python_quote(node: Node):
    """Quote an interpreter Node into a host Scott value, matching the QVar/QLam/QApp eliminators."""
    match node:
        case Var(index=index):
            i = _python_church(index)
            return lambda v: lambda l: lambda a: v(i)
        case Lam(body=body):
            quoted_body = _python_quote(body)
            return lambda v: lambda l: lambda a: l(quoted_body)
        case App(function=function, argument=argument):
            quoted_function = _python_quote(function)
            quoted_argument = _python_quote(argument)
            return lambda v: lambda l: lambda a: a(quoted_function)(quoted_argument)
        case _:
            raise ValueError(f"cannot quote {node!r}")


def _arguments(name: str) -> ast.arguments:
    return ast.arguments(
        posonlyargs=[], args=[ast.arg(arg=name)], kwonlyargs=[], kw_defaults=[], defaults=[],
    )


def _decode_python_pyexpr(value) -> ast.expr:
    """Decode a host (Python) Scott PyExpr value, produced by the self-compiled compiler."""
    def on_var(level):
        return ast.Name(id=f"v{_python_church_to_int(level)}", ctx=ast.Load())

    def on_lam(level):
        return lambda body: ast.Lambda(
            args=_arguments(f"v{_python_church_to_int(level)}"),
            body=_decode_python_pyexpr(body),
        )

    def on_app(function):
        return lambda argument: ast.Call(
            func=_decode_python_pyexpr(function),
            args=[_decode_python_pyexpr(argument)],
            keywords=[],
        )

    return value(on_var)(on_lam)(on_app)


def compiled_compiler():
    """The self-compiled compiler: COMPILE compiled to Python and evaluated as a Python function."""
    return eval(compile_to_source(build(COMPILE)))


def compile_with(compiler, node: Node) -> str:
    """Compile ``node`` using a host-Python compiler function (e.g. the self-compiled one)."""
    result = compiler(_python_church(0))(_python_quote(node))
    return ast.unparse(ast.fix_missing_locations(_decode_python_pyexpr(result)))
