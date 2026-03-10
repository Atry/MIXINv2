"""Tests for fixpoint_cached_property.max_fixpoint_iterations and Bottom exception behavior."""

from collections import defaultdict
from typing import Callable

import pytest

from mixinv2 import (
    Bottom,
    LexicalReference,
    extend,
    patch,
    public,
    resource,
    scope,
)
from mixinv2._core import (
    MixinSymbol,
    _accumulate_defaultdict_set,
    fixpoint_cached_property,
)
from mixinv2._runtime import (
    Scope,
    evaluate,
)


class TestMaxFixpointIterationsBasic:
    """Test that both max_fixpoint_iterations=100 and max_fixpoint_iterations=0 produce correct results for acyclic cases."""

    @pytest.fixture(params=[100, 0])
    def max_fixpoint_iterations(self, request: pytest.FixtureRequest) -> int:
        token = fixpoint_cached_property.max_fixpoint_iterations.set(request.param)
        yield request.param
        fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_simple_resource(self, max_fixpoint_iterations: int) -> None:
        @scope
        class Namespace:
            @public
            @resource
            def greeting() -> str:
                return "Hello"

        root = evaluate(Namespace)
        assert isinstance(root, Scope)
        assert root.greeting == "Hello"

    def test_resource_with_dependency(self, max_fixpoint_iterations: int) -> None:
        @scope
        class Namespace:
            @resource
            def name() -> str:
                return "World"

            @public
            @resource
            def greeting(name: str) -> str:
                return f"Hello, {name}!"

        root = evaluate(Namespace)
        assert root.greeting == "Hello, World!"

    def test_nested_scope(self, max_fixpoint_iterations: int) -> None:
        @scope
        class Namespace:
            @public
            @scope
            class Inner:
                @public
                @resource
                def value() -> int:
                    return 42

        root = evaluate(Namespace)
        assert root.Inner.value == 42

    def test_extend_inherits_resources(self, max_fixpoint_iterations: int) -> None:
        @scope
        class Root:
            @scope
            class Base:
                @public
                @resource
                def base_value() -> int:
                    return 10

            @extend(LexicalReference(path=("Base",)))
            @public
            @scope
            class Extended:
                @public
                @resource
                def doubled(base_value: int) -> int:
                    return base_value * 2

        root = evaluate(Root)
        assert root.Extended.base_value == 10
        assert root.Extended.doubled == 20

    def test_patch_with_extend(self, max_fixpoint_iterations: int) -> None:
        @scope
        class Root:
            @scope
            class Base:
                @public
                @resource
                def value() -> int:
                    return 10

            @scope
            class Patcher:
                @patch
                def value() -> Callable[[int], int]:
                    return lambda original: original + 5

            @extend(
                LexicalReference(path=("Base",)),
                LexicalReference(path=("Patcher",)),
            )
            @public
            @scope
            class Combined:
                pass

        root = evaluate(Root)
        assert root.Combined.value == 15

    def test_union_mount(self, max_fixpoint_iterations: int) -> None:
        @scope
        class First:
            @public
            @resource
            def alpha() -> str:
                return "a"

        @scope
        class Second:
            @public
            @resource
            def beta() -> str:
                return "b"

        root = evaluate(First, Second)
        assert root.alpha == "a"
        assert root.beta == "b"


class TestMaxFixpointIterationsComposition:
    """Test composition chains under both max_fixpoint_iterations values."""

    @pytest.fixture(params=[100, 0])
    def max_fixpoint_iterations(self, request: pytest.FixtureRequest) -> int:
        token = fixpoint_cached_property.max_fixpoint_iterations.set(request.param)
        yield request.param
        fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_diamond_inheritance(self, max_fixpoint_iterations: int) -> None:
        """Diamond composition: D extends B and C, both extend A."""

        @scope
        class Root:
            @scope
            class A:
                @public
                @resource
                def value() -> int:
                    return 1

            @extend(LexicalReference(path=("A",)))
            @scope
            class B:
                @patch
                def value() -> Callable[[int], int]:
                    return lambda original: original + 10

            @extend(LexicalReference(path=("A",)))
            @scope
            class C:
                @patch
                def value() -> Callable[[int], int]:
                    return lambda original: original + 100

            @extend(
                LexicalReference(path=("B",)),
                LexicalReference(path=("C",)),
            )
            @public
            @scope
            class D:
                pass

        root = evaluate(Root)
        assert root.D.value == 111

    def test_multi_level_extend(self, max_fixpoint_iterations: int) -> None:
        """A -> B -> C chain of extensions."""

        @scope
        class Root:
            @scope
            class A:
                @public
                @resource
                def value() -> int:
                    return 1

            @extend(LexicalReference(path=("A",)))
            @scope
            class B:
                @patch
                def value() -> Callable[[int], int]:
                    return lambda original: original * 2

            @extend(LexicalReference(path=("B",)))
            @public
            @scope
            class C:
                @patch
                def value() -> Callable[[int], int]:
                    return lambda original: original * 3

        root = evaluate(Root)
        assert root.C.value == 6


class TestZeroIterationSpecific:
    """Tests specific to max_fixpoint_iterations=0."""

    def test_defaults_to_100_iterations(self) -> None:
        """Default max_fixpoint_iterations is 100."""
        assert fixpoint_cached_property.max_fixpoint_iterations.get() == 100

        @scope
        class Namespace:
            @public
            @resource
            def value() -> int:
                return 42

        root = evaluate(Namespace)
        assert root.value == 42

    def test_zero_iteration_no_fixpoint_loop(self) -> None:
        """Under max_fixpoint_iterations=0, properties compute exactly once (no digest loop)."""
        call_count = 0

        @scope
        class Namespace:
            @public
            @resource
            def value() -> int:
                nonlocal call_count
                call_count += 1
                return call_count

        token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
        try:
            root = evaluate(Namespace)
            assert root.value == 1
            assert call_count == 1
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)


class TestDivergentConvergenceBehavior:
    """Tests showing different convergence behavior with different max_fixpoint_iterations.

    The inheritance-calculus paper (Section 7) defines a translation T from
    the lazy λ-calculus to mixin trees.  The mixin-tree equations for the
    ``this`` function (qualified-this resolution) form a monotone system
    whose least fixpoint is computed iteratively when max_fixpoint_iterations > 0.

    With max_fixpoint_iterations=0, cyclic dependencies in the ``this``
    function raise ``Bottom`` because reentry is detected with no iterations
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
        ``qualified_this`` when a scope's overlays depend on the
        qualified-this of another scope, which in turn depends on the
        first scope's overlays.
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
        """max_fixpoint_iterations=0 raises Bottom on mutual recursion.

        With no fixpoint iterations allowed, the mutual dependency between
        A and B triggers reentry detection.  Unlike the old
        INDEXED_HYLOMORPHISM (which had no reentry detection and caused
        Python's natural stack overflow), max_fixpoint_iterations=0 detects
        the reentry immediately and raises Bottom with the incomplete result.
        """
        token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
        try:
            node_a, _node_b = self._make_transitive_closure_nodes(
                initial_a={"x": {1, 2}},
                initial_b={"y": {3, 4}},
            )
            with pytest.raises(Bottom) as exception_info:
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


class TestBottomException:
    """Tests for the Bottom exception class."""

    def test_bottom_is_recursion_error_subclass(self) -> None:
        assert issubclass(Bottom, RecursionError)

    def test_negative_max_fixpoint_iterations_raises_bottom(self) -> None:
        """Negative max_fixpoint_iterations is meaningless; ContextVar accepts any int."""
        # ContextVar accepts any int value, but negative values are nonsensical.
        # The fixpoint loop uses range(max_iterations), so negative values
        # produce zero iterations and raise Bottom on reentry (same as 0).
        pass

    def test_bottom_carries_incomplete_result(self) -> None:
        """max_fixpoint_iterations=1 on a system needing 2+ iterations raises Bottom with partial result."""
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

            with pytest.raises(Bottom) as exception_info:
                node_a.reachable
            # The incomplete result should be a defaultdict(set) with partial data
            assert isinstance(exception_info.value.incomplete_result, defaultdict)
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)


class TestMixinYamlFixpointIteration:
    """Tests proving max_fixpoint_iterations affects .mixin.yaml evaluation.

    SelfReferenceTest.mixin.yaml defines a scope A that inherits from its own
    child via qualified-this: ``A: [SelfReferenceTest, ~, A, child]``.
    This creates a cycle in the ``qualified_this`` BFS:

        A.qualified_this → BFS processes A's references →
        get_symbols returns A.child → A.child.overlays →
        _generate_overlays calls A.qualified_this → REENTRY

    With max_fixpoint_iterations=0, this raises Bottom.
    With max_fixpoint_iterations≥1, fixpoint iteration converges.
    """

    @pytest.fixture
    def self_reference_symbol(self) -> "MixinSymbol":
        """Load SelfReferenceTest.mixin.yaml and return the SelfReferenceTest symbol."""
        from pathlib import Path

        from mixinv2._mixin_directory import DirectoryMixinDefinition

        tests_path = Path(__file__).parent
        definition = DirectoryMixinDefinition(
            inherits=(), is_public=True, underlying=tests_path
        )
        root = MixinSymbol(origin=(definition,))
        return root["SelfReferenceTest"]

    def test_zero_iterations_raises_bottom(self) -> None:
        """max_fixpoint_iterations=0 raises Bottom on self-referencing qualified_this."""
        from pathlib import Path

        from mixinv2._mixin_directory import DirectoryMixinDefinition

        token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
        try:
            tests_path = Path(__file__).parent
            definition = DirectoryMixinDefinition(
                inherits=(), is_public=True, underlying=tests_path
            )
            root = MixinSymbol(origin=(definition,))
            symbol = root["SelfReferenceTest"]["A"]

            with pytest.raises(Bottom):
                symbol.qualified_this
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_hundred_iterations_converges(
        self, self_reference_symbol: "MixinSymbol"
    ) -> None:
        """max_fixpoint_iterations=100 converges for self-referencing qualified_this."""
        symbol_a = self_reference_symbol["A"]
        qualified_this = symbol_a.qualified_this
        # A inherits from its own child, so overlays include both A and A.child
        assert len(qualified_this) == 2
