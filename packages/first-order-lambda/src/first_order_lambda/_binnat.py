"""Binary naturals (BinNat): an LSB-first lambda-calculus encoding of the naturals, with arithmetic.

A BinNat is a Scott-encoded linked list of booleans (bits), least-significant bit first: its value is
``sum(bit_i << i)``. A bit is a Scott boolean (``TRUE`` = 1, ``FALSE`` = 0). Trailing zero bits are
harmless, so a value has many representations; the operations and ``binnat_to_int`` are correct on all
of them. Unlike a Church numeral, whose successor is O(1) but whose every operation is O(value) (it is
unary), a BinNat is O(log value) in size, so addition, comparison, and multiplication are polynomial
in the number of digits: this is what makes a dynamic program or a graph search written as a lambda
term and run by the interpreter practical rather than exponential.

The arithmetic combinators (``BIN_SUCC``, ``BIN_ADD``, ``BIN_SUB``, ``BIN_MUL``, ``BIN_CMP`` and the
comparisons built on it) are pure lambda terms, recursing over the bit list with ``Y``; the
interpreter runs them, tabling shared subproblems. Python ``int`` decoding is for tests and readouts.

The same encoding also names the compiler's emitted Python identifiers: an identifier is a *list* of
BinNats (an AST path), decoded to an underscore-joined name like ``v_12_3_567``, distinct paths giving
distinct names, so uniqueness is by construction.
"""

from __future__ import annotations

from first_order_lambda._ast import Node
from first_order_lambda._dsl import Builder, app, lam
from first_order_lambda._prelude import AND, FALSE, OR, SCOTT_NIL, TRUE, Y, cons
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


# --- arithmetic: pure lambda terms over LSB-first bit lists, run by the interpreter -------------
# A Scott boolean selects between two branches (``bit then else``); a Scott list is eliminated by
# ``list on_cons on_nil``. The recursions thread a carry (addition), a borrow (subtraction), or a
# comparison verdict from the high bits down, with ``Y`` for the structural recursion over the digits.


def _not(bit: Builder) -> Builder:
    return app(app(bit, FALSE), TRUE)


def _and(left: Builder, right: Builder) -> Builder:
    return app(app(AND, left), right)


def _or(left: Builder, right: Builder) -> Builder:
    return app(app(OR, left), right)


def _xor(left: Builder, right: Builder) -> Builder:
    return app(app(left, _not(right)), right)  # left ? not right : right


def _majority(first: Builder, second: Builder, third: Builder) -> Builder:
    return _or(_and(first, second), _or(_and(first, third), _and(second, third)))


def _bit_equal(left: Builder, right: Builder) -> Builder:
    return app(app(left, right), _not(right))  # left ? right : not right


def _eliminate(value: Builder, on_cons: Builder, on_nil: Builder) -> Builder:
    return app(app(value, on_cons), on_nil)


BIN_ZERO: Builder = SCOTT_NIL
BIN_ONE: Builder = cons(TRUE, SCOTT_NIL)

# add carry a b: ripple-carry addition, both lists LSB-first, treating a missing digit as 0.
_ADD_CARRY: Builder = app(Y, lam(lambda add: lam(lambda carry: lam(lambda a: lam(lambda b: _eliminate(
    a,
    lam(lambda x: lam(lambda xs: _eliminate(
        b,
        lam(lambda y: lam(lambda ys: cons(
            _xor(_xor(x, y), carry),
            app(app(app(add, _majority(x, y, carry)), xs), ys),
        ))),
        cons(_xor(x, carry), app(app(app(add, _and(x, carry)), xs), SCOTT_NIL)),
    ))),
    _eliminate(
        b,
        lam(lambda y: lam(lambda ys: cons(
            _xor(y, carry),
            app(app(app(add, _and(y, carry)), SCOTT_NIL), ys),
        ))),
        app(app(carry, BIN_ONE), SCOTT_NIL),  # both empty: a final carry is the leading 1
    ),
))))))

BIN_ADD: Builder = lam(lambda a: lam(lambda b: app(app(app(_ADD_CARRY, FALSE), a), b)))
BIN_SUCC: Builder = lam(lambda n: app(app(BIN_ADD, n), BIN_ONE))

# pred n: truncated decrement (pred 0 = 0). bit 1 clears to 0; bit 0 borrows from the next digit.
BIN_PRED: Builder = app(Y, lam(lambda pred: lam(lambda n: _eliminate(
    n,
    lam(lambda bit: lam(lambda rest: app(
        app(bit, cons(FALSE, rest)),
        cons(TRUE, app(pred, rest)),
    ))),
    SCOTT_NIL,
))))

# sub borrow a b: truncated subtraction (a - b is 0 when a < b). Borrow out is the majority of
# (not x), y, borrow; a exhausted means the rest underflows, truncated to 0.
_SUB_BORROW: Builder = app(Y, lam(lambda sub: lam(lambda borrow: lam(lambda a: lam(lambda b: _eliminate(
    a,
    lam(lambda x: lam(lambda xs: _eliminate(
        b,
        lam(lambda y: lam(lambda ys: cons(
            _xor(_xor(x, y), borrow),
            app(app(app(sub, _majority(_not(x), y, borrow)), xs), ys),
        ))),
        cons(_xor(x, borrow), app(app(app(sub, _and(_not(x), borrow)), xs), SCOTT_NIL)),
    ))),
    SCOTT_NIL,
))))))

# is_zero n: every digit is 0 (or the list is empty).
BIN_IS_ZERO: Builder = app(Y, lam(lambda is_zero: lam(lambda n: _eliminate(
    n,
    lam(lambda bit: lam(lambda rest: app(app(bit, FALSE), app(is_zero, rest)))),
    TRUE,
))))

# A comparison verdict is a three-way selector ``verdict less equal greater``.
_LESS: Builder = lam(lambda less: lam(lambda equal: lam(lambda greater: less)))
_EQUAL: Builder = lam(lambda less: lam(lambda equal: lam(lambda greater: equal)))
_GREATER: Builder = lam(lambda less: lam(lambda equal: lam(lambda greater: greater)))


def _bit_compare(x: Builder, y: Builder) -> Builder:
    # equal bits compare equal; otherwise x = 1 means greater (1 > 0), x = 0 means less (0 < 1).
    return app(app(_bit_equal(x, y), _EQUAL), app(app(x, _GREATER), _LESS))


# cmp a b: the verdict for a versus b. The high bits dominate, so recurse on the tails first; if they
# are equal the current bit decides, otherwise the tail verdict stands. A missing tail compares as 0.
BIN_CMP: Builder = app(Y, lam(lambda cmp: lam(lambda a: lam(lambda b: _eliminate(
    a,
    lam(lambda x: lam(lambda xs: _eliminate(
        b,
        lam(lambda y: lam(lambda ys: app(
            app(app(app(app(cmp, xs), ys), _LESS), _bit_compare(x, y)),
            _GREATER,
        ))),
        app(app(app(BIN_IS_ZERO, cons(x, xs)), _EQUAL), _GREATER),  # a vs 0
    ))),
    _eliminate(
        b,
        lam(lambda y: lam(lambda ys: app(app(app(BIN_IS_ZERO, cons(y, ys)), _EQUAL), _LESS))),  # 0 vs b
        _EQUAL,  # both empty
    ),
)))))

BIN_LESS: Builder = lam(lambda a: lam(lambda b: app(app(app(app(app(BIN_CMP, a), b), TRUE), FALSE), FALSE)))
BIN_EQUAL: Builder = lam(lambda a: lam(lambda b: app(app(app(app(app(BIN_CMP, a), b), FALSE), TRUE), FALSE)))
BIN_MIN: Builder = lam(lambda a: lam(lambda b: app(app(app(app(app(BIN_CMP, a), b), a), a), b)))
BIN_MAX: Builder = lam(lambda a: lam(lambda b: app(app(app(app(app(BIN_CMP, a), b), b), a), a)))

# sub a b: truncated subtraction. The borrow subtraction is correct only when a >= b (it emits low
# digits before it could detect an underflow), so the verdict gates it: a <= b gives 0, a > b the
# borrow subtraction.
BIN_SUB: Builder = lam(lambda a: lam(lambda b: app(
    app(app(app(app(BIN_CMP, a), b), BIN_ZERO), BIN_ZERO),
    app(app(app(_SUB_BORROW, FALSE), a), b),
)))

# mul a b: shift-and-add. b = bit0 + 2 * rest, so a * b = (bit0 ? a : 0) + (2a) * rest.
BIN_MUL: Builder = app(Y, lam(lambda mul: lam(lambda a: lam(lambda b: _eliminate(
    b,
    lam(lambda bit: lam(lambda rest: app(
        app(BIN_ADD, app(app(bit, a), SCOTT_NIL)),
        app(app(mul, cons(FALSE, a)), rest),
    ))),
    SCOTT_NIL,
)))))
