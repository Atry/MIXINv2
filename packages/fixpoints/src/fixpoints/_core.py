"""Least-fixpoint cached-property infrastructure for mutual recursion.

``fixpoint_cached_property`` and ``fixpoint_dependent`` are drop-in
replacements for ``functools.cached_property`` that resolve mutually
recursive computations by least-fixpoint iteration.  When reentry (a cycle)
is detected, the outermost caller drives a digest loop that re-evaluates
participants until their values stabilize, starting from a configurable
bottom value.
"""

from __future__ import annotations

import itertools
import math
from collections import defaultdict
from contextvars import ContextVar
from enum import Enum
from functools import cached_property
from typing import Callable, ClassVar


class _FixpointContext:
    """Tracks the state of a fixpoint iteration (digest cycle).

    Stored in a ContextVar so that nested/concurrent fixpoint computations
    are isolated per-thread/per-coroutine.
    """

    __slots__ = ("computing", "reentrant", "participant_ids", "participant_refs",
                 "_clearable_attr_names", "approximations")

    def __init__(self, clearable_attr_names: frozenset[str]) -> None:
        self.computing: set[tuple[int, str]] = set()
        self.reentrant: bool = False
        self.participant_ids: set[int] = set()
        self.participant_refs: list[object] = []
        self._clearable_attr_names = clearable_attr_names
        self.approximations: dict[tuple[int, str], object] = {}

    def add_participant(self, instance: object) -> None:
        instance_id = id(instance)
        if instance_id not in self.participant_ids:
            self.participant_ids.add(instance_id)
            self.participant_refs.append(instance)

    def clear_participant_caches(self) -> None:
        """Clear all fixpoint-related cached values on all participants.

        Before clearing, save each value into ``approximations`` so that
        intermediate fixpoint_cached_property computations can use their
        previous iteration's result as an approximation instead of bottom
        when they encounter reentry.
        """
        for instance in self.participant_refs:
            instance_dict = instance.__dict__
            instance_id = id(instance)
            for attr_name in self._clearable_attr_names:
                value = instance_dict.pop(attr_name, None)
                if value is not None:
                    self.approximations[(instance_id, attr_name)] = value


_fixpoint_context_var: ContextVar[_FixpointContext | None] = ContextVar(
    "_fixpoint_context_var", default=None
)


class FixpointRecursionError(RecursionError):
    """Raised when fixpoint iteration is exhausted or reentry is detected with no iterations remaining.

    Carries the best approximation computed so far in ``incomplete_result``.
    As a ``RecursionError`` subclass, existing code that catches ``RecursionError``
    will also catch ``FixpointRecursionError``.
    """

    incomplete_result: object

    def __init__(self, message: str, *, incomplete_result: object) -> None:
        super().__init__(message)
        self.incomplete_result = incomplete_result


_FIXPOINT_SENTINEL = object()

# Registry of attribute names that need clearing during fixpoint digest cycles.
# Populated by fixpoint_cached_property and fixpoint_dependent decorators.
_fixpoint_clearable_attrs: set[str] = set()


def _accumulate_defaultdict_set(
    accumulator: defaultdict[object, set[object]],
    new_result: defaultdict[object, set[object]],
) -> bool:
    """Merge new_result into accumulator (pointwise set union).

    Returns True if accumulator grew (new entries were added).
    """
    changed = False
    for key, values in new_result.items():
        existing = accumulator[key]
        old_size = len(existing)
        existing.update(values)
        if len(existing) > old_size:
            changed = True
    return changed


class FixpointIterationSentinel(Enum):
    UNLIMITED = math.inf


class fixpoint_cached_property:
    """A cached_property that supports mutual-recursion via least fixpoint iteration.

    API-compatible with functools.cached_property. When reentry is detected
    (mutual recursion), returns the previous iteration's approximation
    (or ``bottom()`` on the first iteration). The outermost caller drives
    a digest loop until values stabilize (no reentry occurs in a round).

    Usage::

        @fixpoint_cached_property(bottom=lambda: defaultdict(set))
        def qualified_this(self):
            ...

    The class-level ``max_fixpoint_iterations`` ContextVar controls the
    maximum number of digest rounds.  ``0`` disables fixpoint iteration
    and raises ``FixpointRecursionError`` on reentry.  Default
    ``FixpointIterationSentinel.UNLIMITED`` iterates until convergence or
    until Python's stack is exhausted::

        fixpoint_cached_property.max_fixpoint_iterations.set(0)   # single-pass
        fixpoint_cached_property.max_fixpoint_iterations.set(100) # bounded multi-pass
        fixpoint_cached_property.max_fixpoint_iterations.set(FixpointIterationSentinel.UNLIMITED) # unbounded (default)
    """

    max_fixpoint_iterations: ClassVar[ContextVar[int | FixpointIterationSentinel]] = ContextVar(
        "fixpoint_cached_property.max_fixpoint_iterations", default=FixpointIterationSentinel.UNLIMITED
    )

    def __init__(
        self,
        func: Callable = None,
        *,
        bottom: Callable[[], object],
        accumulate: Callable[[object, object], bool] | None = None,
    ) -> None:
        # Support both @fixpoint_cached_property(bottom=...) and direct call
        self._bottom = bottom
        self._accumulate = accumulate
        if func is not None:
            self.func: Callable = func
            self.attrname: str = func.__name__
            self.__doc__ = func.__doc__
            _fixpoint_clearable_attrs.add(self.attrname)

    def __call__(self, func: Callable) -> "fixpoint_cached_property":
        """Support @fixpoint_cached_property(bottom=...) decorator syntax."""
        self.func = func
        self.attrname = func.__name__
        self.__doc__ = func.__doc__
        _fixpoint_clearable_attrs.add(self.attrname)
        return self

    def __set_name__(self, owner: type, name: str) -> None:
        if not hasattr(self, "attrname"):
            self.attrname = name
        _fixpoint_clearable_attrs.add(self.attrname)

    @classmethod
    def _get_max_iterations(cls) -> int | float:
        raw = cls.max_fixpoint_iterations.get()
        if isinstance(raw, FixpointIterationSentinel):
            return raw.value
        return raw

    def __get__(self, instance: object, owner: type = None) -> object:
        if instance is None:
            return self

        # Fast path: already cached
        cache = instance.__dict__
        value = cache.get(self.attrname, _FIXPOINT_SENTINEL)
        if value is not _FIXPOINT_SENTINEL:
            max_iterations = self._get_max_iterations()
            if max_iterations == 0:
                return value
            # Detect reentry: if this key is currently being computed
            # (on the call stack), accessing its cached approximation
            # means the fixpoint has not converged yet.
            context = _fixpoint_context_var.get()
            if context is not None:
                key = (id(instance), self.attrname)
                if key in context.computing:
                    context.reentrant = True
                    context.add_participant(instance)
            return value

        max_iterations = self._get_max_iterations()
        context = _fixpoint_context_var.get()
        instance_id = id(instance)
        key = (instance_id, self.attrname)

        if context is None:
            # I am the driver — start a digest loop (or single-pass for max_iterations=0)
            context = _FixpointContext(
                clearable_attr_names=frozenset(_fixpoint_clearable_attrs)
            )
            token = _fixpoint_context_var.set(context)
            try:
                if max_iterations == 0:
                    # Zero-iteration mode: compute once with reentry detection.
                    # Reentry raises FixpointRecursionError instead of infinite recursion.
                    context.computing.add(key)
                    result = self.func(instance)
                    cache[self.attrname] = result
                    return result

                approximation = self._bottom()
                accumulator = self._bottom() if self._accumulate is not None else None
                previous_result = _FIXPOINT_SENTINEL
                for iteration in itertools.count():
                    context.computing.add(key)
                    context.add_participant(instance)
                    result = self.func(instance)

                    if not context.reentrant:
                        # No reentry this round — fixpoint reached
                        cache[self.attrname] = result
                        return result

                    if self._accumulate is not None:
                        # Monotonic accumulation: merge each iteration's
                        # result into an accumulator that only grows.
                        # This prevents oscillation when intermediate
                        # computations encounter cycles in varying order.
                        changed = self._accumulate(accumulator, result)
                        if not changed and iteration > 0:
                            cache[self.attrname] = accumulator
                            return accumulator
                        # Use the accumulator as next round's approximation
                        approximation = accumulator
                    else:
                        # Exact equality convergence (original behavior)
                        if result == previous_result:
                            cache[self.attrname] = result
                            return result
                        previous_result = result
                        approximation = result

                    # Cache current approximation, clear all intermediate
                    # caches, and re-run
                    cache[self.attrname] = approximation
                    context.clear_participant_caches()
                    # Restore driver's own approximation
                    cache[self.attrname] = approximation
                    context.computing.clear()
                    context.reentrant = False

                    if iteration + 1 >= max_iterations:
                        raise FixpointRecursionError(
                            f"fixpoint_cached_property '{self.attrname}' did not converge "
                            f"after {max_iterations} iterations",
                            incomplete_result=approximation,
                        )
            finally:
                _fixpoint_context_var.reset(token)
        elif key in context.computing:
            # Reentry detected — return previous approximation or bottom.
            context.reentrant = True
            context.add_participant(instance)
            if max_iterations == 0:
                raise FixpointRecursionError(
                    f"fixpoint_cached_property '{self.attrname}': "
                    f"reentry detected with max_fixpoint_iterations=0",
                    incomplete_result=self._bottom(),
                )
            # Check the instance cache first, then fall back to saved
            # approximations from the previous iteration.
            approximation = cache.get(self.attrname, _FIXPOINT_SENTINEL)
            if approximation is not _FIXPOINT_SENTINEL:
                return approximation
            saved = context.approximations.get(key, _FIXPOINT_SENTINEL)
            if saved is not _FIXPOINT_SENTINEL:
                return saved
            return self._bottom()
        else:
            # Inside a fixpoint context but this is a fresh (instance, attr)
            # pair — compute normally.  Keep the key in ``computing`` only
            # while ``self.func`` runs so that cycles through this key are
            # detected by the ``elif`` branch above.  Once computation
            # finishes, remove the key so the fast-path cache check does
            # not misidentify a later read of this cached value as reentry.
            context.computing.add(key)
            context.add_participant(instance)
            result = self.func(instance)
            context.computing.discard(key)
            cache[self.attrname] = result
            return result

    def __set__(self, instance: object, value: object) -> None:
        """Data descriptor setter to ensure __get__ is always called."""
        instance.__dict__[self.attrname] = value


class _fixpoint_dependent_property:
    """A cached_property that registers its instance as a fixpoint participant.

    Behaves like ``functools.cached_property`` but, when computed inside an
    active fixpoint context, registers the instance so that
    ``clear_participant_caches`` will clear the cached value between
    iterations.  Without this, stale values computed from an incomplete
    fixpoint approximation survive across iterations.
    """

    def __init__(self, func: Callable) -> None:
        self.func = func
        self.attrname = func.__name__
        self.__doc__ = func.__doc__
        _fixpoint_clearable_attrs.add(self.attrname)

    def __set_name__(self, owner: type, name: str) -> None:
        if not hasattr(self, "attrname"):
            self.attrname = name
        _fixpoint_clearable_attrs.add(self.attrname)

    def __get__(self, instance: object, owner: type = None) -> object:
        if instance is None:
            return self

        cache = instance.__dict__
        value = cache.get(self.attrname)
        if value is not None:
            return value

        if fixpoint_cached_property._get_max_iterations() > 0:
            # Register as participant so clear_participant_caches can
            # invalidate this cached value between fixpoint iterations.
            context = _fixpoint_context_var.get()
            if context is not None:
                context.add_participant(instance)

        value = self.func(instance)
        cache[self.attrname] = value
        return value


def fixpoint_dependent(func: Callable) -> _fixpoint_dependent_property:
    """Mark a cached_property as dependent on fixpoint_cached_property values.

    During fixpoint digest cycles, these caches are cleared between iterations
    so they are recomputed with updated approximations.

    Usage::

        @fixpoint_dependent
        @cached_property
        def symbol_kind(self):
            ...

    Or equivalently::

        @fixpoint_dependent
        def symbol_kind(self):
            ...
    """
    if isinstance(func, cached_property):
        return _fixpoint_dependent_property(func.func)
    else:
        return _fixpoint_dependent_property(func)
