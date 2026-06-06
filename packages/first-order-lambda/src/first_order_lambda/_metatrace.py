"""Loops from folding: a code generator over a stream whose loop is tied by the runtime.

``GEN`` is a pure lambda term that maps a Scott stream ``cons h t`` to a quoted output stream
``Yield h (GEN t)`` (and ``nil`` to ``Stop``). It is an ordinary productive recursion with nothing
loop-aware in it. Run on a *cyclic* source (e.g. ``Y (cons 0)``), the recursive ``GEN t`` re-enters
the same interned state, so the runtime (``fixpoint_cached_property`` + interning) ties the back
edge and the output is a *cyclic* quoted stream. The decoder walks that output with a visited set
(as ``render`` does) and emits a Python generator whose ``while`` loop is exactly the folded back
edge. On a finite source the same ``GEN`` yields a finite, loopless generator. The loop in the
compiled program is the runtime's fold of the trace: tabling is the trace cache of a tracing JIT.
"""

from __future__ import annotations

from first_order_lambda._ast import Node
from first_order_lambda._compiler import Z
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._pyast import _church_to_int, _extract

_STREAM_BASE = 6_000_000


def _scott2(tag: int, fields: "list[Builder]") -> Builder:
    def collect(handlers: "list[Builder]") -> Builder:
        if len(handlers) == 2:
            applied = handlers[tag]
            for field in fields:
                applied = app(applied, field)
            return applied
        return lam(lambda handler: collect(handlers + [handler]))

    return collect([])


def _s_yield(value: Builder, rest: Builder) -> Builder:
    return _scott2(0, [value, rest])


_S_STOP: Builder = _scott2(1, [])

# GEN = Z (lambda self. lambda s. s (lambda h. lambda t. Yield h (self t)) Stop)
GEN: Builder = app(
    Z,
    lam(lambda self_recursion: lam(lambda source: app(
        app(
            source,
            lam(lambda head: lam(lambda tail: _s_yield(head, app(self_recursion, tail)))),
        ),
        _S_STOP,
    ))),
)


def generate(stream: Builder) -> Node:
    """Run ``GEN`` on a stream, returning the (possibly cyclic) quoted output stream node."""
    return build(app(GEN, stream))


def decode_generator(node: Node) -> str:
    """Decode a quoted output stream to a Python generator; a folded back edge becomes ``while``."""
    yields: "list[int]" = []
    seen: "dict[int, int]" = {}
    current = node
    cycle_start: "int | None" = None
    while True:
        if id(current) in seen:
            cycle_start = seen[id(current)]
            break
        seen[id(current)] = len(yields)
        tag, fields = _extract(current, (2, 0), _STREAM_BASE)  # Yield arity 2, Stop arity 0
        if tag == 1:  # Stop
            break
        yields.append(_church_to_int(fields[0]))
        current = fields[1]
    if cycle_start is None:
        body = "\n".join(f"    yield {value}" for value in yields) or "    return"
        return "def stream():\n" + body
    prefix = yields[:cycle_start]
    cycle = yields[cycle_start:]
    lines = [f"    yield {value}" for value in prefix]
    lines.append("    while True:")
    lines.extend(f"        yield {value}" for value in cycle)
    return "def stream():\n" + "\n".join(lines)


def compile_stream(stream: Builder) -> str:
    """Compile a Scott stream to Python generator source via GEN and the cycle-aware decoder."""
    return decode_generator(generate(stream))
