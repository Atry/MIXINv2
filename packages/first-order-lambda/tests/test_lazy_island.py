"""The lazy (call-by-name) island tier: a closed normalizing-but-untypable sub-term compiles and reifies.

A call-by-value island must be simply typable (strongly normalizing). The lazy tier admits a closed term
that is untypable yet normalizing (a terminating ``Y``/``Z`` recursion): compiled call-by-name and read
back with the fuel-bounded ``_quote_lazy``, it reifies to the same value the interpreter reaches. This is
what lets the compiler's own recursive hot path (the type checker that decides islands) become a
compiled island rather than staying interpreted.
"""

from __future__ import annotations

from first_order_lambda._compiler import Runtime, value_island_by_name
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, FIBONACCI, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._specialize import compile_callable, is_typable


def test_lazy_island_reifies_a_normalizing_untypable_term() -> None:
    # factorial uses Y, so the term is untypable, but factorial 3 normalizes to church 6.
    node = build(app(FACTORIAL, church(3)))
    assert not is_typable(node)
    reified = value_island_by_name(compile_callable(node, Runtime.CALL_BY_NAME)).run()
    assert _church_to_int(reified) == _church_to_int(node) == 6


def test_lazy_island_agrees_with_the_interpreter_on_fibonacci() -> None:
    node = build(app(FIBONACCI, church(6)))
    assert not is_typable(node)
    reified = value_island_by_name(compile_callable(node, Runtime.CALL_BY_NAME)).run()
    assert _church_to_int(reified) == _church_to_int(node)
