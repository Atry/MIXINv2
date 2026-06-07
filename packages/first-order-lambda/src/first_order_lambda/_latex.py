"""Render a source lambda term to LaTeX, with variable names matching the compiler's output.

The compiler names a parameter ``v{level}`` where a de Bruijn ``Var(i)`` seen at binder depth ``d``
is the level ``d - 1 - i`` and a ``Lam`` binder introduced at depth ``d`` is the level ``d`` (see
``_decode_pyexpr`` and ``COMPILE`` in ``_compiler``). ``term_to_latex`` prints the source syntax with
those same names, so the displayed lambda and the generated Python line up one to one.
"""

from __future__ import annotations

from first_order_lambda._ast import App, Lam, Native, Node, Var


def term_to_latex(node: Node) -> str:
    """The source term as a LaTeX math string (no surrounding ``$``), named to match the compiler."""
    return _latex(node, 0)


def _name(level: int) -> str:
    assert level >= 0, "a closed term references only bound variables, so every level is nonnegative"
    return f"v_{{{level}}}"


def _latex(node: Node, depth: int) -> str:
    match node:
        case Var(index=index):
            return _name(depth - 1 - index)
        case Lam(body=body):
            return f"\\lambda {_name(depth)}.\\, {_latex(body, depth + 1)}"
        case App(function=function, argument=argument):
            return f"{_function(function, depth)}\\, {_argument(argument, depth)}"
        case Native(arity=arity):
            return f"\\langle\\mathrm{{native}}/{arity}\\rangle"
        case _:
            raise TypeError(f"cannot render {node!r}")


def _function(node: Node, depth: int) -> str:
    # A lambda in function position must be parenthesised; an application stays bare (left associative).
    if isinstance(node, Lam):
        return f"({_latex(node, depth)})"
    return _latex(node, depth)


def _argument(node: Node, depth: int) -> str:
    # Only a variable is atomic in argument position; an application or lambda is parenthesised.
    if isinstance(node, Var):
        return _latex(node, depth)
    return f"({_latex(node, depth)})"
