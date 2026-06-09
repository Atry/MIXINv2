"""The lazy island tier: a closed normalizing-but-untypable sub-term compiles and reifies.

A call-by-value island must be simply typable (strongly normalizing). The lazy tier admits a closed term
that is untypable yet normalizing (a terminating ``Y``/``Z`` recursion): compiled by the call-by-name
codegen and read back with the fuel-bounded ``value_island_by_name``, it reifies to the same value the
interpreter reaches. The ``lazy_runtime`` option chooses the thunk semantics, the same codegen either
way: call-by-need (the default) memoises shared sub-results, call-by-name recomputes them. Both are
sound; this checks both reify to the interpreter's value.

This admits MORE islands (closed normalizing-but-untypable DATA sub-terms), not faster compilation of the
recursive hot path: a bare recursive function (a fixpoint combinator, the type checker as a value) has no
finite normal form, so the soundness gate correctly refuses it and it stays interpreted. The wiring test
below also checks the three-way certificate inside the compiler: a normalizing-untypable sub-term becomes
a ``value_island_by_name`` splice, while a non-normalizing one stays interpreted.
"""

from __future__ import annotations

import pytest

from first_order_lambda._compiler import Runtime, interpret_globals
from first_order_lambda._dsl import app, build
from first_order_lambda._prelude import FACTORIAL, FIBONACCI, IDENTITY, SELF_APPLY, Y, church
from first_order_lambda._pyast import _church_to_int
from first_order_lambda._render import render
from first_order_lambda._specialize import SpecializedOption, compile, is_typable, lazy_island


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


@pytest.mark.parametrize("call_by_need", [True, False])
def test_compiler_emits_a_lazy_island_for_a_normalizing_untypable_subterm(call_by_need: bool) -> None:
    """The compiler's three-way certificate: a closed untypable-but-normalizing term becomes a lazy island.

    ``SELF_APPLY`` (``λx. x x``) is closed and untypable (the self-application has no simple type) yet
    already normal, so it has a finite normal form. The specialized output therefore splices it as a
    ``value_island_by_name`` lazy island, and the island reifies to the same value the interpreter
    computes, under both the call-by-need (memoise) and call-by-name (recompute) load-time regimes.
    """
    node = build(SELF_APPLY)
    assert not is_typable(node)
    source = compile(node, SpecializedOption(8))
    assert "value_island_by_name(" in source  # the lazy tier fired
    namespace = dict(interpret_globals(call_by_need=call_by_need))
    exec(source, namespace)  # noqa: S102 - our own generated source
    assert render(namespace["compiled_compiler"]) == render(node)  # faithful to the interpreter


def test_compiler_leaves_a_non_normalizing_subterm_interpreted() -> None:
    """Soundness: a closed untypable term with NO finite normal form is never made a lazy island.

    ``Y IDENTITY`` reduces forever (no normal form), so the eager read-back would diverge. The compiler
    must leave it interpreted (reconstructed with ``make_*``), never spliced as ``value_island_by_name``.
    """
    source = compile(build(app(Y, IDENTITY)), SpecializedOption(8))
    assert "value_island_by_name(" not in source
