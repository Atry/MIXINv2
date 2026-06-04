"""MIXINv2-based configuration for the first-order-lambda interpreter.

The position congruence and its dead-argument rules are the two semantic parameters of the
readout. This module exposes them as composable MIXINv2 resources: ``deadArgumentRules`` is a
``@merge`` that collects ``@patch`` contributions into a tuple, and ``congruence`` is a
``@resource`` derived from the collected rules.

Rule providers are separate ``@scope``s composed at ``evaluate()`` time::

    from mixinv2 import evaluate
    from first_order_lambda._config import (
        FirstOrderLambda,
        WithRecursionArgumentRule,
        WithUnusedParameterRule,
    )

    root = evaluate(FirstOrderLambda, WithRecursionArgumentRule, WithUnusedParameterRule)
    congruence = root.congruence   # DeadSubtermCongruence with both rules

    root_default = evaluate(FirstOrderLambda)
    congruence = root_default.congruence   # IdentityCongruence (no rules patched in)
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Iterator

from mixinv2 import merge, patch, public, resource, scope

from first_order_lambda._congruence import (
    DeadSubtermCongruence,
    IdentityCongruence,
    RecursionArgumentRule,
    UnusedParameterRule,
)

if TYPE_CHECKING:
    from first_order_lambda._congruence import Congruence, DeadArgumentRule


@scope
class FirstOrderLambda:
    """Base configuration scope. Compose with rule-provider scopes to configure the congruence."""

    @public
    @merge
    def deadArgumentRules() -> Callable[[Iterator[DeadArgumentRule]], tuple[DeadArgumentRule, ...]]:
        return lambda rules: tuple(rules)

    @public
    @resource
    def congruence(deadArgumentRules: tuple[DeadArgumentRule, ...]) -> Congruence:
        if deadArgumentRules:
            return DeadSubtermCongruence(rules=deadArgumentRules)
        return IdentityCongruence()


@scope
class WithUnusedParameterRule:
    """Patch: add ``UnusedParameterRule`` to ``deadArgumentRules``."""

    @patch
    def deadArgumentRules() -> DeadArgumentRule:
        return UnusedParameterRule()


@scope
class WithRecursionArgumentRule:
    """Patch: add ``RecursionArgumentRule`` to ``deadArgumentRules``."""

    @patch
    def deadArgumentRules() -> DeadArgumentRule:
        return RecursionArgumentRule()
