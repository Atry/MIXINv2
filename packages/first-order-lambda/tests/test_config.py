"""MIXINv2 module-as-scope configuration for the position congruence.

The dead-argument rules are composable ``@patch`` contributions collected by a ``@merge``
resource. The congruence is derived from the collected rules. These tests pin the composition
and verify that the configured congruence behaves identically to direct construction.
"""

from __future__ import annotations

from mixinv2 import evaluate

from first_order_lambda import _config, WithRecursionArgumentRule, WithUnusedParameterRule
from first_order_lambda._congruence import (
    DeadSubtermCongruence,
    IdentityCongruence,
)
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    CYCLIC_ZEROS,
    IDENTITY,
    KESTREL,
    OMEGA,
    ZERO,
)
from first_order_lambda._readout import readout, render


def test_default_congruence_is_identity() -> None:
    root = evaluate(_config)
    assert isinstance(root.congruence, IdentityCongruence)


def test_single_rule_produces_dead_subterm_congruence() -> None:
    root = evaluate(_config, WithRecursionArgumentRule)
    assert isinstance(root.congruence, DeadSubtermCongruence)
    assert len(root.congruence.rules) == 1


def test_both_rules_composed() -> None:
    root = evaluate(
        _config, WithUnusedParameterRule, WithRecursionArgumentRule
    )
    assert isinstance(root.congruence, DeadSubtermCongruence)
    assert len(root.congruence.rules) == 2


def test_configured_congruence_folds_cyclic_zeros() -> None:
    root = evaluate(_config, WithRecursionArgumentRule)
    rendered = render(readout(CYCLIC_ZEROS, congruence=root.congruence))
    assert "#" in rendered


def test_configured_congruence_keeps_omega_bottom() -> None:
    root = evaluate(
        _config, WithRecursionArgumentRule, WithUnusedParameterRule
    )
    assert render(readout(OMEGA, congruence=root.congruence)) == "⊥"


def test_unused_parameter_rule_erases_discarded_argument() -> None:
    root = evaluate(_config, WithUnusedParameterRule)
    congruence = root.congruence
    discards_identity = build(app(app(KESTREL, ZERO), IDENTITY))
    discards_kestrel = build(app(app(KESTREL, ZERO), KESTREL))
    assert congruence.key(discards_identity) == congruence.key(discards_kestrel)


def test_no_rules_keeps_arguments_distinct() -> None:
    root = evaluate(_config)
    congruence = root.congruence
    discards_identity = build(app(app(KESTREL, ZERO), IDENTITY))
    discards_kestrel = build(app(app(KESTREL, ZERO), KESTREL))
    assert congruence.key(discards_identity) != congruence.key(discards_kestrel)
