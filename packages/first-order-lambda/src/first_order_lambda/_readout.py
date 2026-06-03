"""The Berarducci tree readout (Definition ``def:btree``), as iterates of one monotone ascent.

``berarducci`` resolves each position's head via its single-valued ``shape`` and descends. It
is the same readout under two re-entry policies, two points of the Kleene ascent of the
shape operator:

- ``fold_cycles=False`` is the first-iteration approximation ``T \\uparrow 1`` (``Sbot``): a
  cyclic position re-entered during its own readout returns ``⊥`` (the demand is answered by
  ``T \\uparrow 0 = \\bot``), so a guarded cycle is cut at ``⊥``.
- ``fold_cycles=True`` is the least fixpoint ``lfp`` (``Semp``): the re-entry folds, so a
  guarded cycle becomes a finite rational graph (the output is genuinely cyclic, and
  ``render`` prints it with back-reference labels).

``T \\uparrow 1 \\sqsubseteq lfp``: they agree on acyclic terms and on unproductive cycles
(both ``⊥``), and ``lfp`` is more defined at a guarded cycle, where ``T \\uparrow 1`` has ``⊥``
and ``lfp`` has the folded subtree. The fold is taken only at CLOSED positions, so a folded
back-reference never misreads a free de Bruijn variable. Beta-headed applications are
retained, not collapsed.
"""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import final

from first_order_lambda._ast import Node, ShapeBottom
from first_order_lambda._shape import AppShape, LamShape, VarShape, shape_of


@dataclass(kw_only=True, eq=False)
class TreeNode(ABC):
    """A Berarducci-tree output node. Identity object; mutable so cycles can be tied."""


@final
@dataclass(kw_only=True, eq=False)
class VarLeaf(TreeNode):
    index: int


@final
@dataclass(kw_only=True, eq=False)
class BottomLeaf(TreeNode):
    """The bottom leaf ``⊥``: an unproductive cycle, or a position with no weak-head shape."""


@final
@dataclass(kw_only=True, eq=False)
class LamTree(TreeNode):
    body: TreeNode


@final
@dataclass(kw_only=True, eq=False)
class AppTree(TreeNode):
    function: TreeNode
    argument: TreeNode


def berarducci(node: Node, *, fold_cycles: bool = True) -> TreeNode:
    """Read out the Berarducci tree of ``node``.

    ``fold_cycles=True`` is the least fixpoint ``lfp`` (folds a guarded cycle into a finite
    rational graph); ``fold_cycles=False`` is the first-iteration approximation ``T \\uparrow
    1`` (cuts a cyclic position to ``⊥``).
    """
    return _read(node, {}, {}, fold_cycles)


def _read(
    node: Node,
    memo: dict[int, TreeNode],
    in_progress: dict[int, TreeNode],
    fold_cycles: bool,
) -> TreeNode:
    # Fold (memoise / emit a back-reference) only at CLOSED positions. A position with free
    # de Bruijn variables means different things under different binder contexts, so folding
    # it by node identity would misread those variables across the back-edge. Closed positions
    # carry no free variable, so folding them is exact; open subpositions are rebuilt.
    closed = node.loose_bound == 0
    node_id = id(node)
    if closed:
        folded = in_progress.get(node_id)
        if folded is not None:
            # Re-entry: fold (lfp) or cut to bottom (the first-iteration approximation).
            return folded if fold_cycles else BottomLeaf()
        cached = memo.get(node_id)
        if cached is not None:
            return cached
    head = shape_of(node)
    match head:
        case ShapeBottom.BOTTOM:
            leaf: TreeNode = BottomLeaf()
            if closed:
                memo[node_id] = leaf
            return leaf
        case VarShape(index=index):
            return VarLeaf(index=index)
        case LamShape(body=body):
            lam_tree = LamTree(body=BottomLeaf())
            if closed:
                in_progress[node_id] = lam_tree
            lam_tree.body = _read(body, memo, in_progress, fold_cycles)
            if closed:
                del in_progress[node_id]
                memo[node_id] = lam_tree
            return lam_tree
        case AppShape(function=function, argument=argument):
            app_tree = AppTree(function=BottomLeaf(), argument=BottomLeaf())
            if closed:
                in_progress[node_id] = app_tree
            app_tree.function = _read(function, memo, in_progress, fold_cycles)
            app_tree.argument = _read(argument, memo, in_progress, fold_cycles)
            if closed:
                del in_progress[node_id]
                memo[node_id] = app_tree
            return app_tree
        case _:
            raise TypeError(f"Unknown shape {head!r}")


def _children(tree: TreeNode) -> tuple[TreeNode, ...]:
    match tree:
        case LamTree(body=body):
            return (body,)
        case AppTree(function=function, argument=argument):
            return (function, argument)
        case _:
            return ()


def render(tree: TreeNode) -> str:
    """Render a (possibly cyclic) readout tree, labelling back-reference targets ``#N``."""
    cyclic: set[int] = set()
    on_stack: set[int] = set()
    visited: set[int] = set()

    def scan(node: TreeNode) -> None:
        node_id = id(node)
        if node_id in on_stack:
            cyclic.add(node_id)
            return
        if node_id in visited:
            return
        visited.add(node_id)
        on_stack.add(node_id)
        for child in _children(node):
            scan(child)
        on_stack.discard(node_id)

    scan(tree)

    labels: dict[int, int] = {}
    emitted: set[int] = set()
    next_label = 0

    def emit(node: TreeNode) -> str:
        nonlocal next_label
        node_id = id(node)
        if node_id in cyclic and node_id in emitted:
            return f"#{labels[node_id]}"
        prefix = ""
        if node_id in cyclic:
            labels[node_id] = next_label
            next_label += 1
            emitted.add(node_id)
            prefix = f"#{labels[node_id]}="
        match node:
            case VarLeaf(index=index):
                return f"{prefix}v{index}"
            case BottomLeaf():
                return f"{prefix}⊥"
            case LamTree(body=body):
                return f"{prefix}(λ {emit(body)})"
            case AppTree(function=function, argument=argument):
                return f"{prefix}({emit(function)} {emit(argument)})"
            case _:
                raise TypeError(f"Unknown tree node {node!r}")

    return emit(tree)
