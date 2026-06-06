"""NodeScope: per-node canonical-form computation, the ``Request``-scope pattern for AST nodes.

Each instance receives a ``node`` (the AST position) and a ``childCanonical`` callback (the
memoized recursion) as externs, and exposes ``canonical`` as a ``@resource``. The parent scope
wires the memoization so each interned node is canonicalized at most once per congruence.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable

from mixinv2 import extern, public, resource

from first_order_lambda._congruence import compute_canonical

if TYPE_CHECKING:
    from collections.abc import Hashable

    from first_order_lambda._ast import Node
    from first_order_lambda._congruence import DeadArgumentRule


@extern
def node() -> Node: ...


@extern
def childCanonical() -> Callable[[Node], Hashable]: ...


@public
@resource
def canonical(
    node: Node,
    deadArgumentRules: tuple[DeadArgumentRule, ...],
    childCanonical: Callable[[Node], Hashable],
) -> Hashable:
    return compute_canonical(node, rules=deadArgumentRules, child_canonical=childCanonical)
