"""TEMPORARY scaffolding: monkey-patch tracing for the evaluation-trace appendix.

This installs structured tracing into the MIXINv2 semantic functions WITHOUT
modifying the library source (`mixinv2._core`). It wraps, at runtime, the
underlying functions of the relevant descriptors:

    MixinSymbol.normalized_references  (bases)
    MixinSymbol.qualified_this         (supers / the this-frontier closure)
    MixinSymbol.overrides              (overrides)
    ResolvedReference.get_symbols      (resolve + the per-step this walk)

For the descriptor-based properties we replace only the descriptor's ``.func``,
so the fixpoint / caching machinery in `_core` is left intact and merely calls
our wrapper as its computation. ``get_symbols`` is a plain method, replaced
directly. ``install()`` / ``uninstall()`` are idempotent and restore the
originals exactly.
"""

from __future__ import annotations

import mixinv2._core as _core

# --- trace state ------------------------------------------------------------
ENABLED = False
RECORDS: list[dict] = []
STACK: list[tuple] = []
EDGES: list[tuple] = []
NODES: dict[tuple, dict] = {}


def reset() -> None:
    RECORDS.clear()
    STACK.clear()
    EDGES.clear()
    NODES.clear()


def _trace(function: str, **fields) -> None:
    if ENABLED:
        RECORDS.append({"function": function, **fields})


def _trace_node(node_id: tuple, **fields) -> None:
    if not ENABLED:
        return
    if node_id not in NODES:
        NODES[node_id] = {"function": node_id[0], **fields}
    if STACK:
        edge = (STACK[-1], node_id)
        if edge not in EDGES:
            EDGES.append(edge)


class _trace_frame:
    """Context manager: register a node, record the caller edge, push it."""

    __slots__ = ("node_id",)

    def __init__(self, node_id: tuple, **fields) -> None:
        self.node_id = node_id
        _trace_node(node_id, **fields)

    def __enter__(self):
        if ENABLED:
            STACK.append(self.node_id)
        return self

    def __exit__(self, *exc) -> None:
        if ENABLED and STACK and STACK[-1] == self.node_id:
            STACK.pop()


def _path(symbol) -> tuple:
    """Render a MixinSymbol as a paper-style path tuple, or () for root."""
    try:
        return tuple(symbol.path)
    except Exception:
        return ()


# --- wrappers (mirror the original method bodies, plus tracing) -------------


def _wrap_normalized_references(original):
    def normalized_references(self):
        with _trace_frame(("bases", str(_path(self))), path=_path(self)):
            result = original(self)
        _trace(
            "bases",
            path=_path(self),
            references=tuple(
                {"n": ref.de_bruijn_index, "down": tuple(ref.path)}
                for ref in result
            ),
        )
        return result

    return normalized_references


def _wrap_qualified_this(original):
    def qualified_this(self):
        with _trace_frame(("supers", str(_path(self))), path=_path(self)):
            visited = original(self)
        _trace(
            "supers",
            path=_path(self),
            pairs=tuple(
                sorted(
                    (_path(site), _path(override))
                    for override, sites in visited.items()
                    for site in sites
                )
            ),
        )
        return visited

    return qualified_this


def _wrap_overrides(original):
    def overrides(self):
        with _trace_frame(("overrides", str(_path(self))), path=_path(self)):
            result = original(self)
        _trace(
            "overrides",
            path=_path(self),
            result=tuple(sorted(_path(o) for o in result)),
        )
        return result

    return overrides


def _wrap_get_symbols(original):
    def get_symbols(self, current):
        resolve_id = (
            "resolve",
            f"{_path(current)}|{_path(self.origin_symbol)}"
            f"|{self.de_bruijn_index}|{tuple(self.path)}",
        )
        with _trace_frame(
            resolve_id,
            site=_path(current),
            origin=_path(self.origin_symbol),
            n=self.de_bruijn_index,
            down=tuple(self.path),
        ):
            _trace(
                "resolve",
                site=_path(current),
                origin=_path(self.origin_symbol),
                n=self.de_bruijn_index,
                down=tuple(self.path),
            )
            # Re-implement the de Bruijn walk so each step can be framed and
            # traced; the result is identical to the original get_symbols.
            currents = frozenset((current,))
            definition_site = self.origin_symbol
            for level in range(self.de_bruijn_index):
                this_id = (
                    "this",
                    f"{tuple(sorted(_path(c) for c in currents))}"
                    f"|{_path(definition_site)}|{self.de_bruijn_index - level}",
                )
                with _trace_frame(
                    this_id,
                    frontier_in=tuple(sorted(_path(c) for c in currents)),
                    def_site=_path(definition_site),
                    remaining=self.de_bruijn_index - level,
                ):
                    new_currents = frozenset(
                        qualified_this
                        for current in currents
                        for qualified_this in current.qualified_this[
                            definition_site
                        ]
                    )
                _trace(
                    "this",
                    step=level,
                    remaining=self.de_bruijn_index - level,
                    frontier_in=tuple(sorted(_path(c) for c in currents)),
                    def_site=_path(definition_site),
                    frontier_out=tuple(sorted(_path(c) for c in new_currents)),
                )
                currents = new_currents
                definition_site = definition_site.outer

            results = []
            for current in currents:
                navigated = current
                for key in self.path:
                    navigated = navigated[key]
                results.append(navigated)
        _trace(
            "resolve_result",
            origin=_path(self.origin_symbol),
            n=self.de_bruijn_index,
            down=tuple(self.path),
            targets=tuple(sorted(_path(r) for r in results)),
        )
        return tuple(results)

    return get_symbols


# --- install / uninstall ----------------------------------------------------

_SAVED: dict = {}


def install() -> None:
    """Monkey-patch tracing into _core. Idempotent."""
    if _SAVED:
        return
    symbol = _core.MixinSymbol
    resolved = _core.ResolvedReference

    # Descriptor-backed properties: wrap only the underlying .func, leaving the
    # fixpoint/caching descriptor in place.
    for name, wrapper in (
        ("normalized_references", _wrap_normalized_references),
        ("qualified_this", _wrap_qualified_this),
        ("overrides", _wrap_overrides),
    ):
        descriptor = symbol.__dict__[name]
        original_func = descriptor.func
        _SAVED[("desc", name)] = (descriptor, original_func)
        descriptor.func = wrapper(original_func)

    # Plain method.
    original_get = resolved.__dict__["get_symbols"]
    _SAVED[("method", "get_symbols")] = original_get
    resolved.get_symbols = _wrap_get_symbols(original_get)


def uninstall() -> None:
    """Restore the originals. Idempotent."""
    if not _SAVED:
        return
    for key, saved in _SAVED.items():
        kind, name = key
        if kind == "desc":
            descriptor, original_func = saved
            descriptor.func = original_func
        elif kind == "method":
            _core.ResolvedReference.get_symbols = saved
    _SAVED.clear()
