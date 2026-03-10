"""
MIXINv2: A dependency injection framework with pytest-fixture-like semantics.

Public API
==========

Decorators:
    - :func:`scope`
    - :func:`resource`
    - :func:`patch`
    - :func:`patch_many`
    - :func:`merge`
    - :func:`extern`
    - :func:`public`
    - :func:`eager`
    - :func:`extend`

Runtime:
    - :func:`evaluate`

Exceptions:
    - :class:`Bottom`

Reference types (parameters to :func:`extend`):
    - :class:`AbsoluteReference`
    - :class:`RelativeReference`
    - :class:`LexicalReference`
    - :class:`QualifiedThisReference`
    - :data:`ResourceReference`
"""

from __future__ import annotations

from typing import TYPE_CHECKING

# Public API: decorators and evaluate
from mixinv2._core import eager as eager
from mixinv2._core import extend as extend
from mixinv2._core import extern as extern
from mixinv2._core import merge as merge
from mixinv2._core import patch as patch
from mixinv2._core import patch_many as patch_many
from mixinv2._core import public as public
from mixinv2._core import resource as resource
from mixinv2._core import scope as scope
from mixinv2._core import Bottom as Bottom
from mixinv2._core import fixpoint_cached_property as fixpoint_cached_property
from mixinv2._runtime import evaluate as evaluate

if TYPE_CHECKING:
    from collections.abc import Hashable
    from typing import Protocol, TypeAlias, final

    @final
    class AbsoluteReference(Protocol):
        """An absolute reference to a resource starting from the root scope."""

        path: tuple[Hashable, ...]

        def __init__(self, *, path: tuple[Hashable, ...]) -> None: ...

    @final
    class RelativeReference(Protocol):
        """A reference to a resource relative to the current lexical scope."""

        de_bruijn_index: int
        path: tuple[Hashable, ...]

        def __init__(
            self, *, de_bruijn_index: int, path: tuple[Hashable, ...]
        ) -> None: ...

    @final
    class LexicalReference(Protocol):
        """A lexical reference following the MIXINv2 spec resolution algorithm."""

        path: tuple[Hashable, ...]

        def __init__(self, *, path: tuple[Hashable, ...]) -> None: ...

    @final
    class QualifiedThisReference(Protocol):
        """A qualified this reference: [SelfName, ~, property, path]."""

        self_name: str
        path: tuple[str, ...]

        def __init__(
            self, *, self_name: str, path: tuple[str, ...]
        ) -> None: ...

    ResourceReference: TypeAlias = (
        AbsoluteReference
        | RelativeReference
        | LexicalReference
        | QualifiedThisReference
    )
else:
    from mixinv2._core import AbsoluteReference as AbsoluteReference
    from mixinv2._core import LexicalReference as LexicalReference
    from mixinv2._core import (
        QualifiedThisReference as QualifiedThisReference,
    )
    from mixinv2._core import RelativeReference as RelativeReference
    from mixinv2._core import ResourceReference as ResourceReference
