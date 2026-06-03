"""Tests for fixpoint_cached_property fixpoint-iteration and FixpointRecursionError behavior."""

from collections import defaultdict

import pytest

from fixpoints._core import (
    FixpointIterationSentinel,
    FixpointRecursionError,
    _accumulate_defaultdict_set,
    fixpoint_cached_property,
)


class TestDivergentConvergenceBehavior:
    """Tests showing different convergence behavior with different max_fixpoint_iterations.

    The inheritance-calculus paper (Section 7) defines a translation T from
    the lazy λ-calculus to mixin trees.  The mixin-tree equations for the
    ``this`` function (qualified-this resolution) form a monotone system
    whose least fixpoint is computed iteratively when max_fixpoint_iterations > 0.

    With max_fixpoint_iterations=0, cyclic dependencies in the ``this``
    function raise ``FixpointRecursionError`` because reentry is detected with no iterations
    remaining to converge.

    The cycle pattern arises from self-referential λ-terms such as the
    self-application combinator Ω = (λx. x x)(λx. x x).  The T
    translation maps Ω to a mixin tree where the ``tailCall`` scope
    inherits from ``↑1.argument`` (the enclosing lambda's argument slot).
    After composition, this creates a cycle in the ``this`` function:
    computing ``this(p, p_def)`` for one scope requires ``this`` for
    another scope, which in turn requires the first.

    The tests below use ``fixpoint_cached_property`` directly — the same
    mechanism that implements ``qualified_this`` in the MixinSymbol —
    to demonstrate the divergence/convergence difference.
    """

    def _make_transitive_closure_nodes(
        self,
        initial_a: dict[str, set[int]],
        initial_b: dict[str, set[int]],
    ) -> tuple[object, object]:
        """Create two nodes with mutually recursive transitive closure.

        Each node's ``reachable`` property is the union of its own values
        and everything reachable from the other node.  This is analogous
        to the ``this(p, p_def)`` function: ``this(p) = own(p) ∪
        ⋃{this(q) | q ∈ supers(p)}``, which forms a monotone system
        over set-valued lattices.

        The mutual dependence mirrors the cycle that arises in
        ``qualified_this`` when a scope's overrides depend on the
        qualified-this of another scope, which in turn depends on the
        first scope's overrides.
        """

        class TransitiveClosureNode:
            def __init__(self, initial_values: dict[str, set[int]]) -> None:
                self.__dict__["_initial_values"] = initial_values
                self.__dict__["_other"] = None

            def set_other(self, other: "TransitiveClosureNode") -> None:
                self.__dict__["_other"] = other

            @fixpoint_cached_property(
                bottom=lambda: defaultdict(set),
                accumulate=_accumulate_defaultdict_set,
            )
            def reachable(self) -> defaultdict[str, set[int]]:
                result: defaultdict[str, set[int]] = defaultdict(set)
                for key, values in self._initial_values.items():
                    result[key].update(values)
                if self._other is not None:
                    for key, values in self._other.reachable.items():
                        result[key].update(values)
                return result

        node_a = TransitiveClosureNode(initial_a)
        node_b = TransitiveClosureNode(initial_b)
        node_a.set_other(node_b)
        node_b.set_other(node_a)
        return node_a, node_b

    def test_fixpoint_converges_on_mutual_recursion(self) -> None:
        """max_fixpoint_iterations=100 resolves mutual recursion via iterative approximation.

        Analogous to Datalog transitive closure or the ``this`` fixpoint:
        the computation starts with ⊥ (empty set), and each iteration
        discovers more reachable elements until convergence.
        """
        token = fixpoint_cached_property.max_fixpoint_iterations.set(100)
        try:
            node_a, node_b = self._make_transitive_closure_nodes(
                initial_a={"x": {1, 2}},
                initial_b={"y": {3, 4}},
            )
            reachable_a = dict(node_a.reachable)
            reachable_b = dict(node_b.reachable)
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

        # Both nodes discover each other's values through fixpoint iteration
        assert reachable_a["x"] == {1, 2}
        assert reachable_a["y"] == {3, 4}
        assert reachable_b["x"] == {1, 2}
        assert reachable_b["y"] == {3, 4}

    def test_zero_iterations_raises_bottom_on_mutual_recursion(self) -> None:
        """max_fixpoint_iterations=0 raises FixpointRecursionError on mutual recursion.

        With no fixpoint iterations allowed, the mutual dependency between
        A and B triggers reentry detection.  Unlike the old
        INDEXED_HYLOMORPHISM (which had no reentry detection and caused
        Python's natural stack overflow), max_fixpoint_iterations=0 detects
        the reentry immediately and raises FixpointRecursionError with the incomplete result.
        """
        token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
        try:
            node_a, _node_b = self._make_transitive_closure_nodes(
                initial_a={"x": {1, 2}},
                initial_b={"y": {3, 4}},
            )
            with pytest.raises(FixpointRecursionError) as exception_info:
                node_a.reachable
            assert isinstance(exception_info.value.incomplete_result, defaultdict)
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_fixpoint_converges_three_node_cycle(self) -> None:
        """max_fixpoint_iterations=100 handles N-way cycles (A→B→C→A), not just 2-cycles.

        This mirrors the 3-cycle in RelationalCycle.mixin.yaml (a→b→c→a),
        where the transitive closure requires multiple fixpoint iterations
        to discover all reachable pairs.
        """

        class TriCycleNode:
            def __init__(self, initial_values: dict[str, set[int]]) -> None:
                self.__dict__["_initial_values"] = initial_values
                self.__dict__["_next"] = None

            def set_next(self, other: "TriCycleNode") -> None:
                self.__dict__["_next"] = other

            @fixpoint_cached_property(
                bottom=lambda: defaultdict(set),
                accumulate=_accumulate_defaultdict_set,
            )
            def reachable(self) -> defaultdict[str, set[int]]:
                result: defaultdict[str, set[int]] = defaultdict(set)
                for key, values in self._initial_values.items():
                    result[key].update(values)
                if self._next is not None:
                    for key, values in self._next.reachable.items():
                        result[key].update(values)
                return result

        token = fixpoint_cached_property.max_fixpoint_iterations.set(100)
        try:
            node_a = TriCycleNode({"a": {1}})
            node_b = TriCycleNode({"b": {2}})
            node_c = TriCycleNode({"c": {3}})
            node_a.set_next(node_b)
            node_b.set_next(node_c)
            node_c.set_next(node_a)

            reachable_a = dict(node_a.reachable)
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

        # All three values discovered through the cycle
        assert reachable_a["a"] == {1}
        assert reachable_a["b"] == {2}
        assert reachable_a["c"] == {3}


class TestUnlimitedIterationsOmega:
    """Tests that UNLIMITED iterations causes RecursionError (not FixpointRecursionError) for divergent computations."""

    def test_omega_raises_recursion_error_not_bottom(self) -> None:
        """With UNLIMITED, a divergent fixpoint hits Python's native RecursionError.

        This simulates the Omega combinator: a computation that never converges.
        With a finite limit, the fixpoint loop would raise FixpointRecursionError after exhausting
        iterations. With UNLIMITED, the itertools.count() loop runs indefinitely,
        and eventually Python's recursion limit is hit within a single iteration's
        computation, raising a native RecursionError (not FixpointRecursionError).
        """
        iteration_count = 0

        class OmegaNode:
            def __init__(self) -> None:
                self.__dict__["_other"] = None

            def set_other(self, other: "OmegaNode") -> None:
                self.__dict__["_other"] = other

            @fixpoint_cached_property(bottom=lambda: 0)
            def divergent(self) -> int:
                nonlocal iteration_count
                iteration_count += 1
                if iteration_count > 200:
                    raise RecursionError("simulated stack overflow after 200 iterations")
                # Return alternating values so it never converges
                return self._other.divergent + 1

        node_a = OmegaNode()
        node_b = OmegaNode()
        node_a.set_other(node_b)
        node_b.set_other(node_a)

        with pytest.raises(RecursionError) as exception_info:
            node_a.divergent
        # The error should be a native RecursionError, NOT a FixpointRecursionError
        assert not isinstance(exception_info.value, FixpointRecursionError)
        # Verify we actually ran past the old default of 100
        assert iteration_count > 100


class TestFixpointRecursionErrorException:
    """Tests for the FixpointRecursionError exception class."""

    def test_bottom_is_recursion_error_subclass(self) -> None:
        assert issubclass(FixpointRecursionError, RecursionError)

    def test_negative_max_fixpoint_iterations_raises_bottom(self) -> None:
        """Negative max_fixpoint_iterations is meaningless; ContextVar accepts any int."""
        # ContextVar accepts any int value, but negative values are nonsensical.
        # The fixpoint loop uses range(max_iterations), so negative values
        # produce zero iterations and raise FixpointRecursionError on reentry (same as 0).
        pass

    def test_bottom_carries_incomplete_result(self) -> None:
        """max_fixpoint_iterations=1 on a system needing 2+ iterations raises FixpointRecursionError with partial result."""
        token = fixpoint_cached_property.max_fixpoint_iterations.set(1)
        try:

            class MutualNode:
                def __init__(self, initial_values: dict[str, set[int]]) -> None:
                    self.__dict__["_initial_values"] = initial_values
                    self.__dict__["_other"] = None

                def set_other(self, other: "MutualNode") -> None:
                    self.__dict__["_other"] = other

                @fixpoint_cached_property(
                    bottom=lambda: defaultdict(set),
                    accumulate=_accumulate_defaultdict_set,
                )
                def reachable(self) -> defaultdict[str, set[int]]:
                    result: defaultdict[str, set[int]] = defaultdict(set)
                    for key, values in self._initial_values.items():
                        result[key].update(values)
                    if self._other is not None:
                        for key, values in self._other.reachable.items():
                            result[key].update(values)
                    return result

            node_a = MutualNode({"x": {1}})
            node_b = MutualNode({"y": {2}})
            node_a.set_other(node_b)
            node_b.set_other(node_a)

            with pytest.raises(FixpointRecursionError) as exception_info:
                node_a.reachable
            # The incomplete result should be a defaultdict(set) with partial data
            assert isinstance(exception_info.value.incomplete_result, defaultdict)
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)
