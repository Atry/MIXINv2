"""The fold oracle is a lambda term, agreeing with the Python needs_folding oracle.

``_reduce.NORMALIZES`` is a fuel-bounded normalizer written in the pure calculus; ``normalizes_lambda``
reads its Church-boolean verdict. ``_specialize.needs_folding`` is the Python oracle (its complement:
needs-fold means NOT a finite normal form). These tests pin that the lambda verdict matches the oracle
on the corpus: a finite normal form is positively observed for the normalizing terms (including the
untypable-but-normalizing factorial and fibonacci, which call-by-name reduction reaches through Y), and
the fuel runs out (read as needs-fold) for the cyclic and unproductive ones.
"""

from __future__ import annotations

import pytest

from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    CYCLIC_ZEROS,
    FACTORIAL,
    FIBONACCI,
    IDENTITY,
    KESTREL,
    MULT,
    OMEGA,
    PLUS,
    SUCC,
    church,
)
from first_order_lambda._reduce import normalizes_lambda
from first_order_lambda._specialize import needs_folding

_NORMALIZING = {
    "identity": build(IDENTITY),
    "kestrel": build(KESTREL),
    "church_3": build(church(3)),
    "succ": build(SUCC),
    "plus_2_3": build(app(app(PLUS, church(2)), church(3))),
    "mult_3_4": build(app(app(MULT, church(3)), church(4))),
    "factorial_4": build(app(FACTORIAL, church(4))),
    "fibonacci_5": build(app(FIBONACCI, church(5))),
}

_NEEDS_FOLD = {
    "cyclic_zeros": CYCLIC_ZEROS,
    "omega": OMEGA,
}


@pytest.mark.parametrize("name", sorted(_NORMALIZING))
def test_normalizing_terms_have_a_finite_normal_form(name: str) -> None:
    assert normalizes_lambda(_NORMALIZING[name]) is True
    assert needs_folding(_NORMALIZING[name]) is False  # agrees with the Python oracle


@pytest.mark.parametrize("name", sorted(_NEEDS_FOLD))
def test_cyclic_terms_need_the_fold(name: str) -> None:
    assert normalizes_lambda(_NEEDS_FOLD[name]) is False
    assert needs_folding(_NEEDS_FOLD[name]) is True  # agrees with the Python oracle
