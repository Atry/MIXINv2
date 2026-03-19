"""Tests for Builtin.PythonOperator FFI wrappers.

Verifies that the programmatically generated operator FFI scopes
correctly wrap Python's operator module functions.
"""

from pathlib import Path

import pytest

import mixinv2_library
from mixinv2._mixin_directory import DirectoryMixinDefinition
from mixinv2._runtime import Scope, evaluate


TESTS_PATH = Path(__file__).parent


@pytest.fixture
def operator_scope() -> Scope:
    """Load and evaluate the PythonOperator test fixture."""
    tests_definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=TESTS_PATH
    )
    root = evaluate(mixinv2_library, tests_definition, modules_public=True)
    result = root.PythonOperatorTest
    assert isinstance(result, Scope)
    return result


class TestBinaryArithmetic:
    """Test binary arithmetic operators."""

    def test_add(self, operator_scope: Scope) -> None:
        """3 + 4 = 7"""
        assert operator_scope.addResult == 7

    def test_subtract(self, operator_scope: Scope) -> None:
        """10 - 3 = 7"""
        assert operator_scope.subtractResult == 7

    def test_multiply(self, operator_scope: Scope) -> None:
        """5 * 6 = 30"""
        assert operator_scope.multiplyResult == 30

    def test_true_divide(self, operator_scope: Scope) -> None:
        """7 / 2 = 3.5"""
        assert operator_scope.trueDivideResult == 3.5

    def test_floor_divide(self, operator_scope: Scope) -> None:
        """7 // 2 = 3"""
        assert operator_scope.floorDivideResult == 3

    def test_modulo(self, operator_scope: Scope) -> None:
        """7 % 3 = 1"""
        assert operator_scope.moduloResult == 1

    def test_power(self, operator_scope: Scope) -> None:
        """2 ** 3 = 8"""
        assert operator_scope.powerResult == 8


class TestComparison:
    """Test comparison operators."""

    def test_equal_true(self, operator_scope: Scope) -> None:
        """3 == 3 is True"""
        assert operator_scope.equalTrueResult is True

    def test_equal_false(self, operator_scope: Scope) -> None:
        """3 == 4 is False"""
        assert operator_scope.equalFalseResult is False

    def test_less_than_true(self, operator_scope: Scope) -> None:
        """3 < 4 is True"""
        assert operator_scope.lessThanTrueResult is True

    def test_less_than_false(self, operator_scope: Scope) -> None:
        """4 < 3 is False"""
        assert operator_scope.lessThanFalseResult is False


class TestUnary:
    """Test unary operators."""

    def test_negate(self, operator_scope: Scope) -> None:
        """neg(5) = -5"""
        assert operator_scope.negateResult == -5

    def test_absolute(self, operator_scope: Scope) -> None:
        """abs(-7) = 7"""
        assert operator_scope.absoluteResult == 7

    def test_truth_false(self, operator_scope: Scope) -> None:
        """truth(0) is False"""
        assert operator_scope.truthFalseResult is False

    def test_truth_true(self, operator_scope: Scope) -> None:
        """truth(1) is True"""
        assert operator_scope.truthTrueResult is True

    def test_logical_not(self, operator_scope: Scope) -> None:
        """not_(True) is False"""
        assert operator_scope.logicalNotResult is False


class TestBitwise:
    """Test bitwise operators."""

    def test_bitwise_and(self, operator_scope: Scope) -> None:
        """0b1100 & 0b1010 = 0b1000 = 8"""
        assert operator_scope.bitwiseAndResult == 0b1000

    def test_bitwise_or(self, operator_scope: Scope) -> None:
        """0b1100 | 0b1010 = 0b1110 = 14"""
        assert operator_scope.bitwiseOrResult == 0b1110

    def test_left_shift(self, operator_scope: Scope) -> None:
        """1 << 4 = 16"""
        assert operator_scope.leftShiftResult == 16


class TestSequence:
    """Test sequence operators."""

    def test_concatenate(self, operator_scope: Scope) -> None:
        """'hello ' + 'world' = 'hello world'"""
        assert operator_scope.concatResult == "hello world"


class TestHigherOrder:
    """Test higher-order operators."""

    def test_attribute_get(self, operator_scope: Scope) -> None:
        """'hello'.__class__ is str"""
        assert operator_scope.attributeGetResult is str
