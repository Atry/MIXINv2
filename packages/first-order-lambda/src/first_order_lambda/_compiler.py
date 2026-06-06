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

from first_order_lambda._ast import App, Lam, Node, Var
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import PRED, SUCC, Y, church
from first_order_lambda._pyast import _church_to_int, _extract

_PY_BASE = 5_000_000


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
    Y,
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


def compile_to_source(node: Node) -> str:
    """Compile an interpreter lambda term to Python source: quote, run COMPILE, decode, unparse."""
    compiled = compile_quoted(quote(node))
    return ast.unparse(ast.fix_missing_locations(_decode_pyexpr(compiled)))
