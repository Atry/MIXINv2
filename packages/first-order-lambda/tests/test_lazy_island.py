"""The lazy island tier: a closed normalizing-but-untypable sub-term compiles and reifies.

A call-by-value island must be simply typable (strongly normalizing). The lazy tier admits a closed term
that is untypable yet normalizing (a terminating ``Y``/``Z`` recursion): compiled by the call-by-name
codegen and read back with the fuel-bounded ``value_island_by_name``, it reifies to the same value the
interpreter reaches. The ``lazy_runtime`` option chooses the thunk semantics, the same codegen either
way: call-by-need (the default) memoises shared sub-results, call-by-name recomputes them. Both are
sound; this checks both reify to the interpreter's value. This is what lets the compiler's own recursive
hot path (the type checker that decides islands) become a compiled island rather than staying interpreted.
"""

from __future__ import annotations

import pytest

from first_order_lambda._compiler import Runtime
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, FIBONACCI, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._specialize import is_typable, lazy_island


@pytest.mark.parametrize("lazy_runtime", [Runtime.CALL_BY_NAME, Runtime.CALL_BY_NEED])
def test_lazy_island_reifies_normalizing_untypable_terms(lazy_runtime: Runtime) -> None:
    for term in (app(FACTORIAL, church(3)), app(FACTORIAL, church(4)), app(FIBONACCI, church(6))):
        node = build(term)
        assert not is_typable(node)  # untypable: it recurses through Y
        # but normalizing, so the lazy island reifies to the interpreter's value, under either thunk regime
        assert _church_to_int(lazy_island(node, lazy_runtime).run()) == _church_to_int(node)


def test_lazy_island_rejects_terms_without_a_finite_normal_form() -> None:
    """A bare recursive function has no finite normal form, so read-back would diverge: reject it loudly.

    ``FACTORIAL`` applied to a numeral normalizes, but ``FACTORIAL`` on its own is a closed function whose
    behaviour folds (the Y/Z recursion never terminates structurally). The lazy-island read-back probes a
    function under a fresh binder, which would drive that fold into a divergent loop, so ``lazy_island``
    must refuse it up front (leaving it for the interpreter) rather than crash with a ``RecursionError``.
    """
    bare_recursion = build(FACTORIAL)
    assert not is_typable(bare_recursion)
    with pytest.raises(ValueError, match="finite normal form"):
        lazy_island(bare_recursion)
