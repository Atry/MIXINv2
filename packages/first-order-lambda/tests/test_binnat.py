"""Binary naturals (BinNat): the lambda-calculus encoding the compiler uses to name identifiers.

A BinNat is an LSB-first Scott list of booleans; a symbol is a list of BinNats (an AST path), decoded
to an underscore-joined identifier like ``v_12_3_567``. These tests pin the encode/decode roundtrip
and the rendered identifier shape.
"""

from __future__ import annotations

import pytest
from syrupy.assertion import SnapshotAssertion

from first_order_lambda._binnat import (
    binnat_list,
    binnat_list_to_identifier,
    binnat_to_int,
    int_to_binnat,
)
from first_order_lambda._dsl import build


@pytest.mark.parametrize("value", [0, 1, 2, 3, 5, 12, 255, 567, 1024])
def test_binnat_int_roundtrip(value: int) -> None:
    assert binnat_to_int(build(int_to_binnat(value))) == value


def test_symbol_from_path_renders_underscore_identifier(snapshot: SnapshotAssertion) -> None:
    # A symbol is an AST path (a list of BinNats); the empty path is the root symbol.
    rendered = {
        "root": binnat_list_to_identifier(build(binnat_list([]))),
        "path_12_3_567": binnat_list_to_identifier(build(binnat_list([12, 3, 567]))),
        "path_0_2_1": binnat_list_to_identifier(build(binnat_list([0, 2, 1]))),
    }
    assert rendered == snapshot(name="identifiers")
