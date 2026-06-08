"""Binary naturals (BinNat): an LSB-first lambda-calculus encoding of the naturals, with arithmetic.

A BinNat is an LSB-first Scott list of booleans. These tests pin the encode/decode roundtrip and the
identifier shape, and cross-check the arithmetic combinators (run by the interpreter) against Python
``int`` arithmetic, the reference: a lambda term computing ``a + b`` must agree with ``a + b``.
"""

from __future__ import annotations

import pytest
from syrupy.assertion import SnapshotAssertion

from first_order_lambda._binnat import (
    BIN_ADD,
    BIN_EQUAL,
    BIN_IS_ZERO,
    BIN_LESS,
    BIN_MAX,
    BIN_MIN,
    BIN_MUL,
    BIN_PRED,
    BIN_SUB,
    BIN_SUCC,
    _bit_value,
    binnat_list,
    binnat_list_to_identifier,
    binnat_to_int,
    int_to_binnat,
)
from first_order_lambda._dsl import Builder, app, build


def _unary_int(operation: Builder, value: int) -> int:
    return binnat_to_int(build(app(operation, int_to_binnat(value))))


def _binary_int(operation: Builder, left: int, right: int) -> int:
    return binnat_to_int(build(app(app(operation, int_to_binnat(left)), int_to_binnat(right))))


def _binary_bool(operation: Builder, left: int, right: int) -> bool:
    return bool(_bit_value(build(app(app(operation, int_to_binnat(left)), int_to_binnat(right)))))


_RANGE = range(0, 8)
_PAIRS = [(left, right) for left in _RANGE for right in _RANGE]


@pytest.mark.parametrize("value", [0, 1, 2, 3, 5, 12, 255, 567, 1024])
def test_binnat_int_roundtrip(value: int) -> None:
    assert binnat_to_int(build(int_to_binnat(value))) == value


@pytest.mark.parametrize("value", list(range(0, 17)))
def test_succ_pred_is_zero(value: int) -> None:
    assert _unary_int(BIN_SUCC, value) == value + 1
    assert _unary_int(BIN_PRED, value) == max(0, value - 1)  # truncated at zero
    assert bool(_bit_value(build(app(BIN_IS_ZERO, int_to_binnat(value))))) is (value == 0)


@pytest.mark.parametrize("left, right", _PAIRS)
def test_add_sub_mul_against_python(left: int, right: int) -> None:
    assert _binary_int(BIN_ADD, left, right) == left + right
    assert _binary_int(BIN_SUB, left, right) == max(0, left - right)  # truncated subtraction
    assert _binary_int(BIN_MUL, left, right) == left * right


@pytest.mark.parametrize("left, right", _PAIRS)
def test_compare_and_min_max_against_python(left: int, right: int) -> None:
    assert _binary_bool(BIN_LESS, left, right) is (left < right)
    assert _binary_bool(BIN_EQUAL, left, right) is (left == right)
    assert _binary_int(BIN_MIN, left, right) == min(left, right)
    assert _binary_int(BIN_MAX, left, right) == max(left, right)


def test_symbol_from_path_renders_underscore_identifier(snapshot: SnapshotAssertion) -> None:
    # A symbol is an AST path (a list of BinNats); the empty path is the root symbol.
    rendered = {
        "root": binnat_list_to_identifier(build(binnat_list([]))),
        "path_12_3_567": binnat_list_to_identifier(build(binnat_list([12, 3, 567]))),
        "path_0_2_1": binnat_list_to_identifier(build(binnat_list([0, 2, 1]))),
    }
    assert rendered == snapshot(name="identifiers")
