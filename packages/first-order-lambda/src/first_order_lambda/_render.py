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
from first_order_lambda._shape import (
    AppShape,
    LamShape,
    NativeShape,
    Shape,
    VarShape,
    weak_head_normalize,
)


def render(
    node: Node,
    *,
    fold_cycles: bool = True,
    normalize: Callable[[Node], "Shape | ShapeBottom"] = weak_head_normalize,
    budget: int | None = None,
    max_nodes: int | None = None,
) -> str:
    """Print the rational graph of ``node``, labelling back-reference targets ``#N``.

    ``normalize`` is the structure map ``out``; the default ``weak_head_normalize`` gives the
    Levy-Longo tree, ``head_normalize`` the Boehm tree. Both fold on the same node identity.

    The fold at closed nodes makes a *rational* behaviour finite, but a non-rational one (the open
    inner structure of a fixpoint combinator, which never folds) has an infinite tree; two bounds
    truncate a branch to a ``…`` leaf instead of descending forever. ``budget`` caps the emission
    depth (stack safety on a deep spine) and ``max_nodes`` caps the total nodes emitted (work, since
    the tree also branches). Both ``None`` is unbounded, the exact rational graph.
    """
    labels: dict[int, int] = {}
    on_path: set[int] = set()
    next_label = 0
    emitted = 0

    def emit(current: Node, depth: int) -> str:
        nonlocal next_label, emitted
        if (budget is not None and depth >= budget) or (max_nodes is not None and emitted >= max_nodes):
            return "…"  # a bound reached: a non-rational behaviour, truncated rather than looped
        emitted += 1
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
                body = f"(λ {emit(lam_body, depth + 1)})"
            case AppShape(function=function, argument=argument):
                body = f"({emit(function, depth + 1)} {emit(argument, depth + 1)})"
            case NativeShape(arity=arity, collected=collected):
                spine = "".join(f" {emit(argument, depth + 1)}" for argument in collected)
                body = f"⟨native:{arity}{spine}⟩"
            case _:
                raise TypeError(f"Unknown head {head!r}")
        if closed:
            on_path.discard(key)
            if key in labels:
                body = f"#{labels[key]}={body}"
        return body

    return emit(node, 0)
