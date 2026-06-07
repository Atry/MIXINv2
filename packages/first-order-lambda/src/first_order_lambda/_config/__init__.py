"""MIXINv2 module-as-scope configuration for the first-order-lambda interpreter.

The position congruence and its dead-argument rules are the two semantic parameters of the
readout. This package exposes them as composable MIXINv2 resources: ``deadArgumentRules`` is a
``@merge`` that collects ``@patch`` contributions into a tuple, and ``congruence`` is a
``@resource`` derived from the collected rules.

Rule providers are separate modules composed at ``evaluate()`` time::

    from mixinv2 import evaluate
    from first_order_lambda._config import (
        _config,
        WithRecursionArgumentRule,
        WithUnusedParameterRule,
    )

    root = evaluate(_config, WithRecursionArgumentRule, WithUnusedParameterRule)
    congruence = root.congruence   # DeadSubtermCongruence with both rules

    root_default = evaluate(_config)
    congruence = root_default.congruence   # IdentityCongruence (no rules patched in)
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Iterator

from mixinv2 import merge, public, resource

from first_order_lambda._congruence import (
    DeadSubtermCongruence,
    IdentityCongruence,
)

if TYPE_CHECKING:
    from collections.abc import Hashable

    from first_order_lambda._ast import Node
    from first_order_lambda._congruence import Congruence, DeadArgumentRule


@public
@merge
def deadArgumentRules() -> Callable[[Iterator[DeadArgumentRule]], tuple[DeadArgumentRule, ...]]:
    return lambda rules: tuple(rules)


@public
@resource
def congruence(
    deadArgumentRules: tuple[DeadArgumentRule, ...],
    NodeScope: Callable[..., object],
) -> Congruence:
    if deadArgumentRules:
        canonical_cache: dict[int, Hashable] = {}

        def child_canonical(n: Node) -> Hashable:
            node_id = id(n)
            result = canonical_cache.get(node_id)
            if result is not None:
                return result
            result = NodeScope(node=n, childCanonical=child_canonical).canonical
            canonical_cache[node_id] = result
            return result

        return DeadSubtermCongruence(
            rules=deadArgumentRules, _child_canonical=child_canonical
        )
    return IdentityCongruence()
