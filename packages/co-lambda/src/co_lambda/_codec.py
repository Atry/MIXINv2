"""The input-side codec register: mechanical Python-data -> lambda-term encodings, plus readouts.

This module is one of the four strictly separated kinds (codec / sugar / runtime / pure-lambda
compiler source). Every function here is a MECHANICAL encoding or decoding rule between a Python
data structure and its Scott/Church representation; the loops and non-Builder parameters in this
module are the codec's data payloads, not term-construction macros. This is the closed register the
parameter rule refers to: a Builder-producing function with a non-Builder parameter is legal iff it
lives here (or in the ``_pyast`` codec). Additions are deliberate register changes.

The output-side codec (the reflective Scott Python-AST decoder, ``to_anf_source``, and
``_church_to_int``) lives in ``_pyast``.
"""

from __future__ import annotations

from co_lambda._ast import App, Lam, Node, Var, make_app, make_var
from co_lambda._dsl import Builder, app, lam
from co_lambda._shape import VarShape

# --- Church numerals -------------------------------------------------------------------------------


def church(n: int) -> Builder:
    """The Church numeral ``n`` = ``lambda s. lambda z. s (s ... (s z))`` (``n`` applications)."""
    if n < 0:
        raise ValueError("Church numerals are nonnegative")

    def body(s: Builder, z: Builder) -> Builder:
        acc = z
        for _ in range(n):
            acc = app(s, acc)
        return acc

    return lam(lambda s: lam(lambda z: body(s, z)))


# --- Scott lists and strings ------------------------------------------------------------------------
# The codec carries its own literal constructors for the representations it encodes to (a Scott list
# cell and the Scott booleans used as bits), so encoding depends on no lambda-source module.

_CODEC_SCOTT_CONS: Builder = lam(
    lambda head: lam(lambda tail: lam(lambda on_cons: lam(lambda on_nil: app(app(on_cons, head), tail))))
)
_CODEC_SCOTT_NIL: Builder = lam(lambda on_cons: lam(lambda on_nil: on_nil))
_CODEC_TRUE: Builder = lam(lambda a: lam(lambda b: a))
_CODEC_FALSE: Builder = lam(lambda a: lam(lambda b: b))


def scott_list(elements: "list[Builder]") -> Builder:
    """Encode a Python list of Builders as a Scott list."""
    result: Builder = _CODEC_SCOTT_NIL
    for element in reversed(elements):
        result = app(app(_CODEC_SCOTT_CONS, element), result)
    return result


def char_codes(text: str) -> Builder:
    """The Scott list of character codes for a fixed Python string (a baked-in literal)."""
    return scott_list([church(ord(character)) for character in text])


# --- binary naturals --------------------------------------------------------------------------------


def int_to_binnat(value: int) -> Builder:
    """Encode a non-negative int as a BinNat (an LSB-first Scott list of Scott-boolean bits)."""
    if value < 0:
        raise ValueError("a BinNat is non-negative")
    bits: "list[Builder]" = []
    while value > 0:
        bits.append(_CODEC_TRUE if value & 1 else _CODEC_FALSE)
        value >>= 1
    return scott_list(bits)


def binnat_list(values: "list[int]") -> Builder:
    """Encode a list of non-negative ints as a Scott list of BinNats (an identifier's segments)."""
    return scott_list([int_to_binnat(value) for value in values])


# --- quoted lambda terms ----------------------------------------------------------------------------
# The quoted-source data constructors (QVar/QLam/QApp), each a literal three-handler Scott shape, and
# the ``quote`` reflection from interpreter nodes into that representation.


def q_var(index: Builder) -> Builder:
    return lam(lambda on_var: lam(lambda on_lam: lam(lambda on_app: app(on_var, index))))


def q_lam(body: Builder) -> Builder:
    return lam(lambda on_var: lam(lambda on_lam: lam(lambda on_app: app(on_lam, body))))


def q_app(function: Builder, argument: Builder) -> Builder:
    return lam(lambda on_var: lam(lambda on_lam: lam(lambda on_app: app(app(on_app, function), argument))))


def quote(node: Node) -> Builder:
    """Reflect an interpreter lambda ``Node`` into a quoted-lambda Scott source term."""
    match node:
        case Var(index=index):
            return q_var(church(index))
        case Lam(body=body):
            return q_lam(quote(body))
        case App(function=function, argument=argument):
            return q_app(quote(function), quote(argument))
        case _:
            raise ValueError(f"cannot quote {node!r}")


# --- Church-boolean readout -------------------------------------------------------------------------

_TRUE_MARKER = 7_100_001
_FALSE_MARKER = 7_100_002


def interpret_boolean(node: Node) -> bool:
    """Observe a Church boolean by selecting between two distinct free-variable markers."""
    applied = make_app(make_app(node, make_var(_TRUE_MARKER)), make_var(_FALSE_MARKER))
    shape = applied.weak_head_normal_form
    match shape:
        case VarShape(index=index) if index == _TRUE_MARKER:
            return True
        case VarShape(index=index) if index == _FALSE_MARKER:
            return False
        case _:
            raise ValueError(f"not a Church boolean: {shape!r}")
