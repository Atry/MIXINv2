"""The simple-typability certificate is a lambda term, agreeing with the Python algorithm-W oracle.

``_typecheck.TYPABLE`` is algorithm-W (STLC) written in the pure calculus and run by the interpreter on
the quoted term; ``is_typable_lambda`` reads its Church-boolean verdict. ``_specialize.is_typable`` is
the Python ``_Inference`` port that specifies the same judgement and serves here as the oracle. These
tests pin that the lambda certificate matches the oracle on the typable/untypable corpus and on the
compiler itself, so the certificate that drives specialization can be the lambda term, not Python.
"""

from __future__ import annotations

import pytest

from first_order_lambda._ast import make_lam, make_var
from first_order_lambda._compiler import COMPILE
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import (
    EXP,
    FACTORIAL,
    FIBONACCI,
    IDENTITY,
    IS_ZERO,
    KESTREL,
    MULT,
    OMEGA,
    PLUS,
    PRED,
    SELF_APPLY,
    SUCC,
    Y,
    church,
)
from first_order_lambda._specialize import is_typable
from first_order_lambda._typecheck import is_typable_lambda, typable_bu_lambda

_TYPABLE = {
    "identity": build(IDENTITY),
    "kestrel": build(KESTREL),
    "church_0": build(church(0)),
    "church_3": build(church(3)),
    "succ": build(SUCC),
    "pred": build(PRED),
    "is_zero": build(IS_ZERO),
    "plus": build(PLUS),
    "mult": build(MULT),
    "exp": build(EXP),
    "plus_2_3": build(app(app(PLUS, church(2)), church(3))),
    "lambda_bound_var": make_lam(make_var(0)),
}

# Untypable means the occurs check fires: the self-application ``x x`` constrains ``alpha = alpha ->
# beta``, so Y/Omega and the recursive terms built on them are not simply typable. (A free variable is
# NOT here: algorithm-W gives it a fresh type, so an open term is typable but not closed; closedness is
# the separate ``CLOSED`` certificate's concern, checked in test_lambda_analysis.)
_UNTYPABLE = {
    "self_apply": build(SELF_APPLY),
    "Y": build(Y),
    "omega": OMEGA,
    "factorial": build(FACTORIAL),
    "fibonacci": build(FIBONACCI),
}


@pytest.mark.parametrize("name", sorted(_TYPABLE))
def test_lambda_certificate_accepts_typable_terms(name: str) -> None:
    assert is_typable_lambda(_TYPABLE[name]) is True
    assert is_typable(_TYPABLE[name]) is True  # agrees with the Python oracle


@pytest.mark.parametrize("name", sorted(_UNTYPABLE))
def test_lambda_certificate_rejects_untypable_terms(name: str) -> None:
    assert is_typable_lambda(_UNTYPABLE[name]) is False
    assert is_typable(_UNTYPABLE[name]) is False  # agrees with the Python oracle


def test_lambda_certificate_rejects_the_compiler() -> None:
    # COMPILE is untypable (its Z fixpoint self-applies); the failure short-circuit keeps the lambda
    # certificate fast on this large term, agreeing with the oracle.
    node = build(COMPILE)
    assert is_typable_lambda(node) is False
    assert is_typable(node) is False


# The bottom-up principal-typing fold ``TYPABLE_BU`` is the certificate the island specializer
# consults (it types every sub-term once, reusing children's results, so removing the island depth
# bound stays affordable). It must agree with the same Python algorithm-W oracle on the corpus and,
# crucially, on the compiler's closed sub-terms, since that is where it decides islands.
@pytest.mark.parametrize("name", sorted(_TYPABLE))
def test_bottom_up_certificate_accepts_typable_terms(name: str) -> None:
    assert typable_bu_lambda(_TYPABLE[name]) is True
    assert is_typable(_TYPABLE[name]) is True


@pytest.mark.parametrize("name", sorted(_UNTYPABLE))
def test_bottom_up_certificate_rejects_untypable_terms(name: str) -> None:
    assert typable_bu_lambda(_UNTYPABLE[name]) is False
    assert is_typable(_UNTYPABLE[name]) is False
