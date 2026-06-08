"""Binary naturals (BinNat) for the lambda-calculus compiler's identifiers.

A BinNat is a Scott-encoded linked list of booleans (bits), least-significant bit first: its value is
``sum(bit_i << i)``. A bit is a Scott boolean (``TRUE`` = 1, ``FALSE`` = 0). The compiler builds the
ids that name its emitted Python identifiers out of BinNats with ``cons`` alone (no Church
arithmetic), and Python decodes them. An identifier is a *list* of BinNats, decoded to an
underscore-joined name like ``v_12_3_567``: the ``v`` prefix makes any segment list a valid Python
identifier, and a distinct segment list yields a distinct name, so uniqueness is by construction.
"""

from __future__ import annotations

from first_order_lambda._ast import Node
from first_order_lambda._dsl import Builder
from first_order_lambda._prelude import FALSE, SCOTT_NIL, TRUE, cons
from first_order_lambda._pyast import _decode_scott_list, _extract

# A free-variable band used as a meta marker when probing a Scott boolean (a bit). Disjoint from the
# bands ``_pyast`` uses, so a probed bit's only free variables are these markers.
_BIT_BASE = 8_500_000


def _bit_value(node: Node) -> int:
    # A Scott boolean applied to two nullary handlers exposes handler 0 for TRUE, handler 1 for FALSE.
    tag, _ = _extract(node, (0, 0), _BIT_BASE)
    return 1 if tag == 0 else 0


def binnat_to_int(node: Node) -> int:
    """Decode a BinNat (an LSB-first Scott list of bits) to a non-negative int."""
    value = 0
    for position, bit in enumerate(_decode_scott_list(node)):
        value += _bit_value(bit) << position
    return value


def binnat_list_to_identifier(node: Node, prefix: str = "v") -> str:
    """Decode a Scott list of BinNats to an underscore-joined identifier, e.g. ``v_12_3_567``."""
    segments = [binnat_to_int(segment) for segment in _decode_scott_list(node)]
    return "_".join([prefix, *(str(segment) for segment in segments)])


# --- lambda-term construction helpers (build BinNats and BinNat lists as Builders) --------------

def int_to_binnat(value: int) -> Builder:
    """Build a BinNat (an LSB-first list of bits) for a non-negative int."""
    if value < 0:
        raise ValueError("a BinNat is non-negative")
    bits: "list[Builder]" = []
    while value > 0:
        bits.append(TRUE if value & 1 else FALSE)
        value >>= 1
    result: Builder = SCOTT_NIL
    for bit in reversed(bits):
        result = cons(bit, result)
    return result


def binnat_list(values: "list[int]") -> Builder:
    """Build a Scott list of BinNats from a list of non-negative ints (an identifier's segments)."""
    result: Builder = SCOTT_NIL
    for value in reversed(values):
        result = cons(int_to_binnat(value), result)
    return result
