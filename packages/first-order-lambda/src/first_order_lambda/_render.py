"""Render the rational graph of a term by tabling ``weak_head_normalize`` directly.

The graph of a term is the part of the coalgebra ``(nodes, weak_head_normalize)`` reachable from it;
there is no separate readout structure to build. ``render`` walks ``weak_head_normalize`` from the root,
tabling closed nodes by identity (interning makes that a pointer test), and prints the graph with
explicit back-references for cycles:

- ``fold_cycles=True`` is the least fixpoint: a closed node re-entered during its own descent folds
  to a back-reference ``#N``, so a guarded cycle prints as a finite cyclic graph. Its only leaves
  are variables and the meaningless ``⊥``.
- ``fold_cycles=False`` is the finite-budget first iterate ``T \\uparrow 1``: a re-entry is cut to a
  distinct ``∅`` leaf (a productive cycle the budget stopped), kept separate from ``⊥`` (an
  unproductive cycle, a node with no constructor).

The fold/cut is taken only at CLOSED nodes, so a back-reference never misreads a free de Bruijn
variable; open subnodes are reprinted.
"""

from __future__ import annotations

from typing import Callable

from first_order_lambda._ast import Node, ShapeBottom
from first_order_lambda._shape import AppShape, LamShape, Shape, VarShape, weak_head_normalize


def render(
    node: Node,
    *,
    fold_cycles: bool = True,
    normalize: Callable[[Node], "Shape | ShapeBottom"] = weak_head_normalize,
) -> str:
    """Print the rational graph of ``node``, labelling back-reference targets ``#N``.

    ``normalize`` is the structure map ``out``; the default ``weak_head_normalize`` gives the
    Levy-Longo tree, ``head_normalize`` the Boehm tree. Both fold on the same node identity.
    """
    labels: dict[int, int] = {}
    on_path: set[int] = set()
    next_label = 0

    def emit(current: Node) -> str:
        nonlocal next_label
        closed = current.loose_bound == 0
        key = id(current)
        if closed and key in on_path:
            # Re-entry at a guarded node: fold to a back-reference (lfp), or cut to ∅ (the
            # first-iteration reading), kept distinct from the meaningless ⊥.
            if not fold_cycles:
                return "∅"
            if key not in labels:
                labels[key] = next_label
                next_label += 1
            return f"#{labels[key]}"
        if closed:
            on_path.add(key)
        head = normalize(current)
        match head:
            case ShapeBottom.BOTTOM:
                body = "⊥"
            case VarShape(index=index):
                body = f"v{index}"
            case LamShape(body=lam_body):
                body = f"(λ {emit(lam_body)})"
            case AppShape(function=function, argument=argument):
                body = f"({emit(function)} {emit(argument)})"
            case _:
                raise TypeError(f"Unknown head {head!r}")
        if closed:
            on_path.discard(key)
            if key in labels:
                body = f"#{labels[key]}={body}"
        return body

    return emit(node)
