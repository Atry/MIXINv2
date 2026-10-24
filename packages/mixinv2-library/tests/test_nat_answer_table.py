"""Generate the Nat case study's machine-recorded answer table for the paper.

Runs the executable case study (the ArithmeticTest / CartesianProductTest
entries that compose the ToPython FFI, and the FFI-free NatArithmeticTest
core shown verbatim in the paper) and writes
paper/generated-nat-answers.tex: one item per behavioral claim of the case
study, each stating the query and the recorded outcome. The final item is
an FFI-free metalanguage witness: iterating the bases step of eq:bases from
the paper's core `equal` path reaches a written `True` definition in
finitely many hops.
"""

from collections import deque
from pathlib import Path

import mixinv2_library
from mixinv2._mixin_directory import DirectoryMixinDefinition
from mixinv2._runtime import Scope, evaluate

TESTS_PATH = Path(__file__).parent
_OUTPUT = (
    Path(__file__).resolve().parents[3] / "paper" / "generated-nat-answers.tex"
)
_WALK_CAP = 2000


def _mathlabel(segment) -> str:
    return rf"\text{{``{segment}''}}"


def _path(path: tuple) -> str:
    if not path:
        return "()"
    return "(" + ", ".join(_mathlabel(s) for s in path) + ")"


def _value_set(values) -> str:
    rendered = ", ".join(
        rf"\text{{{value}}}" for value in sorted(values, key=repr)
    )
    return rf"\{{{rendered}\}}"


def _sym_at(root_symbol, full_path: tuple):
    symbol = root_symbol
    for key in full_path:
        symbol = symbol.get(key)
        if symbol is None:
            return None
    return symbol


def _reaches_label(root_symbol, start_path: tuple, target_label: str):
    """Breadth-first bases walk (one eq:bases step per hop: resolve every
    reference of every override at the enclosing scope) until a path whose
    last label is ``target_label`` is reached."""
    seen = {tuple(start_path)}
    queue = deque([(tuple(start_path), 0)])
    visited = 0
    while queue:
        path, hops = queue.popleft()
        visited += 1
        if visited > _WALK_CAP:
            raise ValueError(f"bases walk exceeded {_WALK_CAP} nodes")
        if path and path[-1] == target_label:
            return path, hops
        symbol = _sym_at(root_symbol, path)
        site = _sym_at(root_symbol, path[:-1])
        if symbol is None or site is None:
            continue
        for override in symbol.overrides:
            for reference in override.normalized_references:
                for target in reference.get_symbols(site):
                    target_path = tuple(target.path)
                    if target_path not in seen:
                        seen.add(target_path)
                        queue.append((target_path, hops + 1))
    raise ValueError(
        f"no written {target_label!r} reachable from {start_path}"
    )


def test_generate_nat_answer_table() -> None:
    tests_definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=TESTS_PATH
    )
    root = evaluate(mixinv2_library, tests_definition, modules_public=True)

    arithmetic = root.ArithmeticTest
    assert isinstance(arithmetic, Scope)
    cartesian = root.CartesianProductTest
    assert isinstance(cartesian, Scope)

    sum_values = arithmetic.threePlusFour.sum.pythonValues
    equal_values = arithmetic.threePlusFourEqualsSeven.equal.pythonValues
    product_values = cartesian.NatOneOrTwoPlusThreeOrFour.sum.pythonValues
    self_equal_values = cartesian.NatResultEqualitySelf.equal.pythonValues
    assert sum_values == frozenset({7})
    assert equal_values == frozenset({True})
    assert product_values == frozenset({4, 5, 6})
    assert self_equal_values == frozenset({True, False})

    witness_path, witness_hops = _reaches_label(
        root.symbol,
        ("NatArithmeticTest", "threePlusFourEqualsSeven", "equal"),
        "True",
    )

    lines = [
        "\\begin{enumerate}",
        (
            "  \\item The sum of the case study's addition: the ToPython"
            " readback of the path "
            f"${_path(('ArithmeticTest', 'threePlusFour', 'sum'))}$"
            f" is ${_value_set(sum_values)}$."
        ),
        (
            "  \\item The equality check: the readback of "
            f"${_path(('ArithmeticTest', 'threePlusFourEqualsSeven', 'equal'))}$"
            f" is ${_value_set(equal_values)}$, so $(3+4) = 7$ holds in the"
            " executed encoding."
        ),
        (
            "  \\item The Cartesian-product semantics: the readback of "
            f"${_path(('CartesianProductTest', 'NatOneOrTwoPlusThreeOrFour', 'sum'))}$"
            f" is ${_value_set(product_values)}$, the pointwise sums of"
            " $\\{1, 2\\}$ and $\\{3, 4\\}$."
        ),
        (
            "  \\item The relational equality: the readback of "
            f"${_path(('CartesianProductTest', 'NatResultEqualitySelf', 'equal'))}$"
            f" is ${_value_set(self_equal_values)}$: comparing the set-valued"
            " sum with itself observes both outcomes, one per pair of drawn"
            " values."
        ),
        (
            "  \\item The FFI-free witness: from the core path "
            f"${_path(('NatArithmeticTest', 'threePlusFourEqualsSeven', 'equal'))}$"
            " shown in the paper, iterating the $\\bases$ step of"
            " equation~(\\ref{eq:bases}) reaches the written definition "
            f"${_path(witness_path)}$ in {witness_hops} hops: the mixin that"
            " the reference resolves to inherits \\mintinline{yaml}{True}."
        ),
        "\\end{enumerate}",
    ]
    _OUTPUT.write_text("\n".join(lines) + "\n")
    print(f"Wrote {_OUTPUT}")
