"""Render a source lambda term to LaTeX with readable bound-variable names.

A binder is named by its de Bruijn level (its depth at introduction): the binder introduced at depth
``d`` is level ``d``, and a ``Var(i)`` seen at depth ``d`` refers to level ``d - 1 - i``. Each binder
thus has a distinct level, hence a distinct readable name (``x``, ``y``, ``z``, ...), so the rendering
is unambiguous and reads naturally. The compiler names the same binder ``v{level}`` in the emitted
Python, so the lambda's name at level ``k`` corresponds to the Python parameter ``v{k}``.
"""

from __future__ import annotations

from co_lambda._ast import App, Lam, Native, Node, Var

# Readable bound-variable names indexed by de Bruijn level; deeper levels fall back to a subscript.
_READABLE_NAMES = (
    "x", "y", "z", "w", "u", "s", "t", "p", "q", "r",
    "k", "m", "n", "a", "b", "c", "d", "e", "g", "h",
)


def term_to_latex(node: Node) -> str:
    """The source term as a LaTeX math string (no surrounding ``$``), with readable names."""
    return _latex(node, 0)


def _name(level: int) -> str:
    assert level >= 0, "a closed term references only bound variables, so every level is nonnegative"
    if level < len(_READABLE_NAMES):
        return _READABLE_NAMES[level]
    return f"x_{{{level - len(_READABLE_NAMES) + 1}}}"


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
