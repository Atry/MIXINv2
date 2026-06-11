"""Binary naturals (BinNat): an LSB-first lambda-calculus encoding of the naturals, with arithmetic.

A BinNat is a Scott-encoded linked list of booleans (bits), least-significant bit first: its value is
``sum(bit_i << i)``. A bit is a Scott boolean (``TRUE`` = 1, ``FALSE`` = 0). Trailing zero bits are
harmless, so a value has many representations; the operations are correct on all of them. Unlike a
Church numeral, whose every operation is O(value) (it is unary), a BinNat is O(log value) in size, so
addition, comparison, and multiplication are polynomial in the number of digits.

This module is pure lambda calculus: every top-level binding is a ``Builder`` (a ``@curry``-decorated
``def`` IS a Builder, an object-level abstraction applied with ``app``). The Python-int encodings
(``int_to_binnat``, ``binnat_list``) and readouts (``binnat_to_int``, ``binnat_list_to_identifier``)
live in ``_codec``.

BinNat is also the type checker's type-variable id type: fresh ids get O(log) ``BIN_EQUAL`` comparison
during unification, where Church-id arithmetic would be O(id).
"""

from __future__ import annotations

from co_lambda._dsl import Builder, app, curry, lam
from co_lambda._prelude import AND, FALSE, OR, SCOTT_NIL, TRUE, Y
from co_lambda._sugar import ap, cons

# A Scott boolean selects between two branches (``bit then else``); a Scott list is eliminated by
# ``list on_cons on_nil``. The recursions thread a carry (addition), a borrow (subtraction), or a
# comparison verdict from the high bits down, with ``Y`` for the structural recursion over the digits.


@curry
def _not(bit: Builder) -> Builder:
    return ap(bit, FALSE, TRUE)


@curry
def _xor(left: Builder, right: Builder) -> Builder:
    return ap(left, app(_not, right), right)  # left ? not right : right


@curry
def _majority(first: Builder, second: Builder, third: Builder) -> Builder:
    return ap(
        OR,
        ap(AND, first, second),
        ap(OR, ap(AND, first, third), ap(AND, second, third)),
    )


@curry
def _bit_equal(left: Builder, right: Builder) -> Builder:
    return ap(left, right, app(_not, right))  # left ? right : not right


BIN_ZERO: Builder = SCOTT_NIL
BIN_ONE: Builder = cons(TRUE, SCOTT_NIL)

# add carry a b: ripple-carry addition, both lists LSB-first, treating a missing digit as 0.
_ADD_CARRY: Builder = app(Y, lam(lambda add: lam(lambda carry: lam(lambda a: lam(lambda b: ap(
    a,
    lam(lambda x: lam(lambda xs: ap(
        b,
        lam(lambda y: lam(lambda ys: cons(
            ap(_xor, ap(_xor, x, y), carry),
            ap(add, ap(_majority, x, y, carry), xs, ys),
        ))),
        cons(ap(_xor, x, carry), ap(add, ap(AND, x, carry), xs, SCOTT_NIL)),
    ))),
    ap(
        b,
        lam(lambda y: lam(lambda ys: cons(
            ap(_xor, y, carry),
            ap(add, ap(AND, y, carry), SCOTT_NIL, ys),
        ))),
        ap(carry, BIN_ONE, SCOTT_NIL),  # both empty: a final carry is the leading 1
    ),
))))))

BIN_ADD: Builder = lam(lambda a: lam(lambda b: ap(_ADD_CARRY, FALSE, a, b)))
BIN_SUCC: Builder = lam(lambda n: ap(BIN_ADD, n, BIN_ONE))

# pred n: truncated decrement (pred 0 = 0). bit 1 clears to 0; bit 0 borrows from the next digit.
BIN_PRED: Builder = app(Y, lam(lambda pred: lam(lambda n: ap(
    n,
    lam(lambda bit: lam(lambda rest: ap(
        bit,
        cons(FALSE, rest),
        cons(TRUE, app(pred, rest)),
    ))),
    SCOTT_NIL,
))))

# sub borrow a b: truncated subtraction (a - b is 0 when a < b). Borrow out is the majority of
# (not x), y, borrow; a exhausted means the rest underflows, truncated to 0.
_SUB_BORROW: Builder = app(Y, lam(lambda sub: lam(lambda borrow: lam(lambda a: lam(lambda b: ap(
    a,
    lam(lambda x: lam(lambda xs: ap(
        b,
        lam(lambda y: lam(lambda ys: cons(
            ap(_xor, ap(_xor, x, y), borrow),
            ap(sub, ap(_majority, app(_not, x), y, borrow), xs, ys),
        ))),
        cons(ap(_xor, x, borrow), ap(sub, ap(AND, app(_not, x), borrow), xs, SCOTT_NIL)),
    ))),
    SCOTT_NIL,
))))))

# is_zero n: every digit is 0 (or the list is empty).
BIN_IS_ZERO: Builder = app(Y, lam(lambda is_zero: lam(lambda n: ap(
    n,
    lam(lambda bit: lam(lambda rest: ap(bit, FALSE, app(is_zero, rest)))),
    TRUE,
))))

# A comparison verdict is a three-way selector ``verdict less equal greater``.
_LESS: Builder = lam(lambda less: lam(lambda equal: lam(lambda greater: less)))
_EQUAL: Builder = lam(lambda less: lam(lambda equal: lam(lambda greater: equal)))
_GREATER: Builder = lam(lambda less: lam(lambda equal: lam(lambda greater: greater)))


@curry
def _bit_compare(x: Builder, y: Builder) -> Builder:
    # equal bits compare equal; otherwise x = 1 means greater (1 > 0), x = 0 means less (0 < 1).
    return ap(ap(_bit_equal, x, y), _EQUAL, ap(x, _GREATER, _LESS))


# cmp a b: the verdict for a versus b. The high bits dominate, so recurse on the tails first; if they
# are equal the current bit decides, otherwise the tail verdict stands. A missing tail compares as 0.
BIN_CMP: Builder = app(Y, lam(lambda cmp: lam(lambda a: lam(lambda b: ap(
    a,
    lam(lambda x: lam(lambda xs: ap(
        b,
        lam(lambda y: lam(lambda ys: ap(
            ap(cmp, xs, ys),
            _LESS,
            ap(_bit_compare, x, y),
            _GREATER,
        ))),
        ap(ap(BIN_IS_ZERO, cons(x, xs)), _EQUAL, _GREATER),  # a vs 0
    ))),
    ap(
        b,
        lam(lambda y: lam(lambda ys: ap(ap(BIN_IS_ZERO, cons(y, ys)), _EQUAL, _LESS))),  # 0 vs b
        _EQUAL,  # both empty
    ),
)))))

BIN_LESS: Builder = lam(lambda a: lam(lambda b: ap(BIN_CMP, a, b, TRUE, FALSE, FALSE)))
BIN_EQUAL: Builder = lam(lambda a: lam(lambda b: ap(BIN_CMP, a, b, FALSE, TRUE, FALSE)))
BIN_MIN: Builder = lam(lambda a: lam(lambda b: ap(BIN_CMP, a, b, a, a, b)))
BIN_MAX: Builder = lam(lambda a: lam(lambda b: ap(BIN_CMP, a, b, b, a, a)))

# sub a b: truncated subtraction. The borrow subtraction is correct only when a >= b (it emits low
# digits before it could detect an underflow), so the verdict gates it: a <= b gives 0, a > b the
# borrow subtraction.
BIN_SUB: Builder = lam(lambda a: lam(lambda b: ap(
    BIN_CMP, a, b,
    BIN_ZERO,
    BIN_ZERO,
    ap(_SUB_BORROW, FALSE, a, b),
)))

# mul a b: shift-and-add. b = bit0 + 2 * rest, so a * b = (bit0 ? a : 0) + (2a) * rest.
BIN_MUL: Builder = app(Y, lam(lambda mul: lam(lambda a: lam(lambda b: ap(
    b,
    lam(lambda bit: lam(lambda rest: ap(
        BIN_ADD,
        ap(bit, a, SCOTT_NIL),
        ap(mul, cons(FALSE, a), rest),
    ))),
    SCOTT_NIL,
)))))
