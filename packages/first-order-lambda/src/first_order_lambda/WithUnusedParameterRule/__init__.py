"""Patch: add ``UnusedParameterRule`` to ``deadArgumentRules``."""

from __future__ import annotations

from mixinv2 import patch

from first_order_lambda._congruence import DeadArgumentRule, UnusedParameterRule


@patch
def deadArgumentRules() -> DeadArgumentRule:
    return UnusedParameterRule()
