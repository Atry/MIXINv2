"""Tests for fixpoint_cached_property.max_fixpoint_iterations and FixpointRecursionError exception behavior."""

from typing import Callable

import pytest

from fixpoints._core import (
    FixpointIterationSentinel,
    fixpoint_cached_property,
)
from mixinv2 import (
    FixpointRecursionError,
    LexicalReference,
    extend,
    patch,
    public,
    resource,
    scope,
)
from mixinv2._core import MixinSymbol
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

    def test_defaults_to_unlimited_iterations(self) -> None:
        """Default max_fixpoint_iterations is FixpointIterationSentinel.UNLIMITED."""
        assert fixpoint_cached_property.max_fixpoint_iterations.get() is FixpointIterationSentinel.UNLIMITED

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


class TestMixinYamlFixpointIteration:
    """Tests proving max_fixpoint_iterations affects .mixin.yaml evaluation.

    SelfReferenceTest.mixin.yaml defines a scope A that inherits from its own
    child via qualified-this: ``A: [SelfReferenceTest, ~, A, child]``.
    This creates a cycle in the ``qualified_this`` BFS:

        A.qualified_this → BFS processes A's references →
        get_symbols returns A.child → A.child.overrides →
        _generate_overrides calls A.qualified_this → REENTRY

    With max_fixpoint_iterations=0, this raises FixpointRecursionError.
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
        """max_fixpoint_iterations=0 raises FixpointRecursionError on self-referencing qualified_this."""
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

            with pytest.raises(FixpointRecursionError):
                symbol.qualified_this
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_hundred_iterations_converges(
        self, self_reference_symbol: "MixinSymbol"
    ) -> None:
        """max_fixpoint_iterations=100 converges for self-referencing qualified_this."""
        symbol_a = self_reference_symbol["A"]
        qualified_this = symbol_a.qualified_this
        # A inherits from its own child, so overrides include both A and A.child
        assert len(qualified_this) == 2


class TestLetXEqualsXInX:
    """Tests for LetXEqualsXInX.mixin.yaml: translation T of `let x = x in x`.

    In the λ-calculus, `let x = x in x` diverges under β-reduction.
    Translation T gives: {x ↦ {result ↦ x.result}, result ↦ x.result}

    With max_fixpoint_iterations=0 (single-pass, like LC): raises FixpointRecursionError on cycle.
    With max_fixpoint_iterations=100 (multi-pass, lfp): converges to ∅ children on result.
    """

    @pytest.fixture
    def let_x_equals_x_in_x_symbol(self) -> "MixinSymbol":
        """Load LetXEqualsXInX.mixin.yaml and return the LetXEqualsXInX symbol."""
        from pathlib import Path

        from mixinv2._mixin_directory import DirectoryMixinDefinition

        tests_path = Path(__file__).parent
        definition = DirectoryMixinDefinition(
            inherits=(), is_public=True, underlying=tests_path
        )
        root = MixinSymbol(origin=(definition,))
        return root["LetXEqualsXInX"]

    def test_zero_iterations_raises_bottom(self) -> None:
        """max_fixpoint_iterations=0 raises FixpointRecursionError on x.qualified_this, matching LC divergence."""
        from pathlib import Path

        from mixinv2._mixin_directory import DirectoryMixinDefinition

        token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
        try:
            tests_path = Path(__file__).parent
            definition = DirectoryMixinDefinition(
                inherits=(), is_public=True, underlying=tests_path
            )
            root = MixinSymbol(origin=(definition,))
            symbol = root["LetXEqualsXInX"]

            with pytest.raises(FixpointRecursionError):
                # x inherits from x.result via qualified this, creating cycle:
                # x.qualified_this → BFS → x.result.overrides →
                # _generate_overrides → x.qualified_this → REENTRY
                symbol["x"].qualified_this
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_zero_iterations_result_also_raises_bottom(self) -> None:
        """max_fixpoint_iterations=0 raises FixpointRecursionError on result.qualified_this too."""
        from pathlib import Path

        from mixinv2._mixin_directory import DirectoryMixinDefinition

        token = fixpoint_cached_property.max_fixpoint_iterations.set(0)
        try:
            tests_path = Path(__file__).parent
            definition = DirectoryMixinDefinition(
                inherits=(), is_public=True, underlying=tests_path
            )
            root = MixinSymbol(origin=(definition,))
            symbol = root["LetXEqualsXInX"]

            with pytest.raises(FixpointRecursionError):
                symbol["result"].qualified_this
        finally:
            fixpoint_cached_property.max_fixpoint_iterations.reset(token)

    def test_hundred_iterations_converges(
        self, let_x_equals_x_in_x_symbol: "MixinSymbol"
    ) -> None:
        """max_fixpoint_iterations=100 converges: result has ∅ children."""
        result_symbol = let_x_equals_x_in_x_symbol["result"]
        # Under lfp, the cycle converges: x.result inherits from itself,
        # yielding ∅ children (no abstraction shape found)
        qualified_this = result_symbol.qualified_this
        assert len(qualified_this) == 2
        # result has no children (∅ properties = divergence in LC semantics)
        assert list(result_symbol.keys()) == []
