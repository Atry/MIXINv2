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
from enum import Enum, auto

from first_order_lambda._ast import App, Lam, Node, Var
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import FALSE, PRED, SUCC, TRUE, church
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


# Quoted Python expression: five constructors (PyVar/PyLam/PyApp/PyForce/PyThunk).
def _py_var(level: Builder) -> Builder:
    return _scott(5, 0, [level])


def _py_lam(level: Builder, body: Builder) -> Builder:
    return _scott(5, 1, [level, body])


def _py_app(function: Builder, argument: Builder) -> Builder:
    return _scott(5, 2, [function, argument])


def _py_force(expr: Builder) -> Builder:
    return _scott(5, 3, [expr])


def _py_thunk(expr: Builder) -> Builder:
    return _scott(5, 4, [expr])


# sub a b = a - b, by applying PRED to a, b times.
_SUB: Builder = lam(lambda a: lam(lambda b: app(app(b, PRED), a)))

# Target wrappers, selected by the option (a Church boolean ``thunked``): the lazy target wraps a
# variable and a function in PyForce and an argument in PyThunk; the eager target wraps with identity.
_FORCE_WRAP: Builder = lam(lambda expr: _py_force(expr))
_THUNK_WRAP: Builder = lam(lambda expr: _py_thunk(expr))
_IDENTITY_WRAP: Builder = lam(lambda expr: expr)


def _select_wrap(thunked: Builder, lazy_wrap: Builder) -> Builder:
    # thunked is a Church boolean: it picks lazy_wrap when lazy (TRUE), identity when eager (FALSE).
    return app(app(thunked, lazy_wrap), _IDENTITY_WRAP)


# COMPILE = lambda thunked. Z (lambda self. lambda d. lambda q.
#   q (lambda i. wrapVar (PyVar (sub d (succ i))))                    -- QVar i
#     (lambda b. PyLam d (self (succ d) b))                          -- QLam b
#     (lambda f. lambda a. PyApp (wrapFun (self d f)) (wrapArg (self d a))))  -- QApp f a
# wrapVar = wrapFun = (thunked ? PyForce : id); wrapArg = (thunked ? PyThunk : id).
COMPILE: Builder = lam(lambda thunked: app(
    Z,
    lam(lambda self_recursion: lam(lambda depth: lam(lambda quoted: app(app(app(
        quoted,
        lam(lambda index: app(
            _select_wrap(thunked, _FORCE_WRAP),
            _py_var(app(app(_SUB, depth), app(SUCC, index))),
        )),
        ),
        lam(lambda body: _py_lam(depth, app(app(self_recursion, app(SUCC, depth)), body))),
        ),
        lam(lambda function: lam(lambda argument: _py_app(
            app(_select_wrap(thunked, _FORCE_WRAP), app(app(self_recursion, depth), function)),
            app(_select_wrap(thunked, _THUNK_WRAP), app(app(self_recursion, depth), argument)),
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


def _arguments(name: str) -> ast.arguments:
    return ast.arguments(
        posonlyargs=[], args=[ast.arg(arg=name)], kwonlyargs=[], kw_defaults=[], defaults=[],
    )


def _no_args() -> ast.arguments:
    return ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[])


def _decode_pyast(node: Node) -> ast.expr:
    """Decode a Scott Python expression (PyVar/PyLam/PyApp/PyForce/PyThunk) to a real ``ast`` node.

    This is generic: the target-specific shape (force/thunk wrapping) was decided by the lambda term,
    so the decoder just renders each constructor, with no target branching.
    """
    tag, fields = _extract(node, (1, 2, 2, 1, 1), _PY_BASE)
    match tag:
        case 0:  # PyVar level
            return ast.Name(id=f"v{_church_to_int(fields[0])}", ctx=ast.Load())
        case 1:  # PyLam level body
            return ast.Lambda(args=_arguments(f"v{_church_to_int(fields[0])}"), body=_decode_pyast(fields[1]))
        case 2:  # PyApp function argument
            return ast.Call(func=_decode_pyast(fields[0]), args=[_decode_pyast(fields[1])], keywords=[])
        case 3:  # PyForce expr -> force(expr)
            return ast.Call(
                func=ast.Name(id="force", ctx=ast.Load()), args=[_decode_pyast(fields[0])], keywords=[],
            )
        case 4:  # PyThunk expr -> Thunk(lambda: expr)
            return ast.Call(
                func=ast.Name(id="Thunk", ctx=ast.Load()),
                args=[ast.Lambda(args=_no_args(), body=_decode_pyast(fields[0]))],
                keywords=[],
            )
        case _:
            raise ValueError(f"unknown PyExpr tag {tag}")


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
        raise NotImplementedError("call-by-need codegen (explicit memoising thunks) is not built yet")
    raise ValueError("the interpret target is interpreted; it has no compiled runtime globals")


def compile_to_source(node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile an interpreter lambda term to Python source for the given compiled target.

    Call-by-value yields a strict expression; call-by-name yields the expression with the lambda
    term's ``force``/``Thunk`` wrapping. The interpret target is interpreted, not compiled.
    """
    compiled = compile_quoted(_option(runtime), quote(node))
    return ast.unparse(ast.fix_missing_locations(_decode_pyast(compiled)))


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


def _python_bool(value: bool):
    """A host (Python) Church boolean, matching the eager (FALSE) / lazy (TRUE) compile option."""
    return (lambda a: lambda b: a) if value else (lambda a: lambda b: b)


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

    def on_force(expr):
        return ast.Call(func=ast.Name(id="force", ctx=ast.Load()), args=[_decode_python_pyexpr(expr)], keywords=[])

    def on_thunk(expr):
        return ast.Call(
            func=ast.Name(id="Thunk", ctx=ast.Load()),
            args=[ast.Lambda(args=_no_args(), body=_decode_python_pyexpr(expr))],
            keywords=[],
        )

    return value(on_var)(on_lam)(on_app)(on_force)(on_thunk)


def compiled_compiler():
    """The self-compiled compiler: COMPILE compiled to Python (eager) and evaluated as a function."""
    return eval(compile_to_source(build(COMPILE)))


def compile_with(compiler, node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile ``node`` using a host-Python compiler function (e.g. the self-compiled one)."""
    result = compiler(_python_bool(runtime is Runtime.CALL_BY_NAME))(_python_church(0))(_python_quote(node))
    return ast.unparse(ast.fix_missing_locations(_decode_python_pyexpr(result)))
