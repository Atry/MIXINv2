"""The runtime: the execution host and the MINIMAL API a generated program may reference.

This module is one of the four strictly separated kinds (codec / sugar / runtime / pure-lambda
compiler source). It holds everything operational that compiled artifacts and the analyses rely on:

* the lazy-thunk runtime of the call-by-name/need targets (``force``/``Thunk``), and the
  call-by-need memo-cell sentinel;
* the NbE read-back behind the compiled islands (``_Neutral`` and the one convention-parameterized
  ``_quote``), and the island ``Native`` wrappers ``value_island`` / ``value_island_by_name``;
* the ``interpret`` boundary (a reconstructed term handed back to the interpreter);
* the ``RUNTIME_API`` declaration, the single authoritative vocabulary of names emitted code may
  reference, from which every delivery channel (``interpret_globals``, ``call_by_need_globals``,
  the generated-module header) is derived;
* the host stack helpers (``run_in_large_stack``, ``recursion_headroom``) that give the
  interpreter's recursion the headroom the compiler-scale graphs need.
"""

from __future__ import annotations

import sys
import threading

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Callable, Iterator, final

from co_lambda._ast import App, Lam, Node, Var, make_app, make_lam, make_native, make_var

# --- the lazy-thunk runtime of the compiled call-by-name / call-by-need targets ------------------
# The call-by-name target's emitted Python refers to the free names ``force`` and ``Thunk``. An
# argument is a thunk recomputed on each ``force`` (call-by-name) or computed once and shared
# (call-by-need), matching the interpreter's weak-head reduction so every normalizing term computes
# its value.


class _Thunk:
    """A delayed computation; ``force`` evaluates it."""

    __slots__ = ("_fn", "__dict__")

    def __init__(self, fn) -> None:
        self._fn = fn


class _LazyThunk(_Thunk):
    @property
    def value(self):
        return self._fn()  # call-by-name: recompute on every force


class _NeedThunk(_Thunk):
    @property
    def value(self):  # call-by-need: compute once and share (memoise)
        memo = self.__dict__
        if "_memo" not in memo:
            memo["_memo"] = self._fn()
        return memo["_memo"]


def force(value):
    return value.value if isinstance(value, _Thunk) else value


_SENTINEL_NAME = "CALL_BY_NEED_SENTINEL"


class _CallByNeedSentinel:
    """The unforced marker stored in a memo cell before its thunk computes."""

    def __repr__(self) -> str:
        return _SENTINEL_NAME


_CALL_BY_NEED_SENTINEL = _CallByNeedSentinel()


# --- the interpret boundary -----------------------------------------------------------------------


def interpret(node: Node) -> Node:
    """The interpret boundary: a reconstructed term handed back to the interpreter.

    The node is the value; the interpreter computes its weak head normal form lazily when the result
    is observed (decoded, rendered, or applied at the node level). This is the runtime hook a compiled
    island is spliced around in a specialized program.
    """
    return node


# --- universal reflect/reify (NbE read-back): the islands' boundary -------------------------------
# An island is a closed certified sub-term compiled to Python and run; its host normal form is quoted
# back to a PURE Scott node (Var/Lam/App), so the interpreter folds around it and the generic
# ``_pyast.decode`` reads it (no residual ``Native`` escapes into the output). The read-back is
# church-agnostic: the same walk reifies a Church numeral, a Scott value, or a function. The two
# compiled calling conventions differ only mechanically (force or not, thunked or bare neutral
# arguments, fuel or not), so ONE ``_quote`` is parameterized by a convention.


class _Neutral:
    """A neutral host value in NbE read-back: a bound variable (by de Bruijn level) applied to host
    arguments. It is the only non-callable an island value meets when probed under binders."""

    __slots__ = ("level", "spine")

    def __init__(self, level: int, spine: "tuple" = ()) -> None:
        self.level = level
        self.spine = spine

    def __call__(self, argument) -> "_Neutral":
        return _Neutral(self.level, (*self.spine, argument))


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class _ReadBackConvention:
    """How ``_quote`` probes host values for one compiled calling convention."""

    force_value: "Callable[[object], object]"
    neutral_argument: "Callable[[int], object]"
    spend: "Callable[[int], int]"


def _quote(host, depth: int, convention: _ReadBackConvention, fuel: int) -> Node:
    """Quote a host value (a compiled normal form) to a pure Scott node: a binder per function layer,
    a neutral read as a variable-headed spine. The eager convention terminates because by-value
    islands are strongly normalizing; the lazy convention is fuel-bounded so a term the normalization
    check's fuel was too small to reject fails loudly instead of diverging."""
    fuel = convention.spend(fuel)
    value = convention.force_value(host)
    if isinstance(value, _Neutral):
        node: Node = make_var(depth - 1 - value.level)
        for argument in value.spine:
            node = make_app(node, _quote(argument, depth, convention, fuel))
        return node
    return make_lam(_quote(value(convention.neutral_argument(depth)), depth + 1, convention, fuel))


_EAGER_READ_BACK = _ReadBackConvention(
    force_value=lambda value: value,
    neutral_argument=_Neutral,
    spend=lambda fuel: fuel,
)

_LAZY_ISLAND_READBACK_FUEL = 1_000_000


def _spend_lazy_fuel(fuel: int) -> int:
    if fuel <= 0:
        raise ValueError("lazy island read-back exceeded its fuel; the term may not normalize")
    return fuel - 1


_LAZY_READ_BACK = _ReadBackConvention(
    force_value=force,
    neutral_argument=lambda depth: _LazyThunk(lambda: _Neutral(depth)),
    spend=_spend_lazy_fuel,
)


def value_island(compiled_value) -> Node:
    """A by-value island as an interpreter ``Node``: run the compiled (strongly normalizing) term and
    quote its host normal form back to a pure Scott node, so the interpreter drives it in place of
    interpreting the subtree. Faithfulness is convergence to the same value, not structural identity."""
    return make_native(lambda: _quote(compiled_value, 0, _EAGER_READ_BACK, 0), 0)


def value_island_by_name(compiled_value) -> Node:
    """A call-by-name island as an interpreter ``Node``: run the compiled, normalizing (but not
    necessarily typable) term and quote its lazy normal form back to a pure Scott node. The dual of
    ``value_island`` for the lazy tier, sharing the read-back; faithfulness is convergence to the
    same value."""
    return make_native(lambda: _quote(compiled_value, 0, _LAZY_READ_BACK, _LAZY_ISLAND_READBACK_FUEL), 0)


# --- node_case: the one runtime node-observation primitive ----------------------------------------
# A local host-compiled analysis (a closed analysis lambda compiled to a call-by-need island, e.g.
# IS_CLOSED / TYPABLE_BU / NORMALIZES) consumes a SOURCE term. To run in host it must observe the
# runtime node it is applied to; ``node_case`` is the ONLY primitive that lets the lambda do so -- a
# PURE structural dispatch on the node's LITERAL Var / Lam / App constructor (NO reduction: it matches
# the interner node as built, since quoted source is a normal-form tree). It is provided as a value the
# compiled island takes as a free variable and applies, so it follows the call-by-need value protocol of
# CODEGEN_NEED: a value is a 0-arg thunk forced by ``()``; a forced function takes one thunk argument and
# returns a value. ``node_case node on_var on_lam on_app`` forces ``node``, then applies ``on_var`` to
# the de Bruijn index (as a Church numeral), ``on_lam`` to the body node, or ``on_app`` to the function
# then argument nodes -- each child handed back as a thunk yielding the child node, so the analysis
# recurses through ``node_case`` again. Host execution interns nothing; only the analysis's small result,
# read back at the island boundary, is interned.


def _cbn_apply(function_value, argument_thunk):
    """Call-by-need application: force the function value to a callable, apply it to the argument thunk,
    returning the result value (itself a thunk)."""
    return function_value()(argument_thunk)


def _church_call_by_need(count: int):
    """The Church numeral ``count`` as a forced call-by-need function value: ``\\f x. f^count x``."""
    def take_f(f_thunk):
        def value_in_f():
            def take_x(x_thunk):
                accumulator = x_thunk
                for _ in range(count):
                    accumulator = _cbn_apply(f_thunk, accumulator)
                return accumulator
            return take_x
        return value_in_f
    return take_f


def _node_case_dispatch(node_thunk, on_var, on_lam, on_app):
    """Force the node and apply the matching handler value (literal constructor dispatch, no reduction)."""
    node = node_thunk()
    match node:
        case Var(index=index):
            return _cbn_apply(on_var, lambda: _church_call_by_need(index))
        case Lam(body=body):
            return _cbn_apply(on_lam, lambda: body)
        case App(function=function, argument=argument):
            return _cbn_apply(_cbn_apply(on_app, lambda: function), lambda: argument)
        case _:
            raise ValueError(f"node_case: expected a Var/Lam/App node, got {node!r}")


def _node_case_value():
    """``node_case`` as a forced call-by-need function value: curried over node, on_var, on_lam, on_app."""
    def take_node(node_thunk):
        def value_after_node():
            def take_var(on_var):
                def value_after_var():
                    def take_lam(on_lam):
                        def value_after_lam():
                            def take_app(on_app):
                                return _node_case_dispatch(node_thunk, on_var, on_lam, on_app)
                            return take_app
                        return value_after_lam
                    return take_lam
                return value_after_var
            return take_var
        return value_after_node
    return take_node


# The call-by-need VALUE (a 0-arg thunk) the compiled island binds and forces.
node_case = _node_case_value


# === The minimal runtime API ======================================================================
# The COMPLETE vocabulary a generated program may reference as free names, the single authoritative
# declaration. Every delivery channel below (``interpret_globals``, ``call_by_need_globals``, the
# generated-module header) is DERIVED from this table, and the runtime-API gate test asserts every
# generated module's free names are members. Growing the runtime is a deliberate API change: edit
# this declaration (and the paper's description of the runtime), never add a name at a call site.
RUNTIME_API: "dict[str, object]" = {
    "make_var": make_var,
    "make_lam": make_lam,
    "make_app": make_app,
    "interpret": interpret,
    "value_island": value_island,
    "value_island_by_name": value_island_by_name,
    "force": force,
    "Thunk": _NeedThunk,  # the default lazy regime; a loader may pre-bind the call-by-name _LazyThunk
    "node_case": node_case,  # the one node-observation primitive, for host-compiled local analyses
    _SENTINEL_NAME: _CALL_BY_NEED_SENTINEL,
}

# The interpret-headed subset (an A-normal-form module binding ``compiled_compiler``): everything
# except the call-by-need memo sentinel, which only the whole-program need MODULE refers to.
_INTERPRET_HEADED_NAMES = (
    "make_var", "make_lam", "make_app", "interpret", "value_island",
    "value_island_by_name", "force", "Thunk",
)


def interpret_globals(call_by_need: bool = True) -> dict:
    """The evaluation globals for interpret-headed source, derived from ``RUNTIME_API``.

    ``call_by_need`` (the default) keeps the memoising ``_NeedThunk``; ``call_by_need=False`` binds
    the recompute-on-force ``_LazyThunk`` (call-by-name). The lazy regime is this load-time ``Thunk``
    choice: the generated source is identical either way and both reach the same normal form, so only
    time and memory differ, never the output."""
    delivered = {name: RUNTIME_API[name] for name in _INTERPRET_HEADED_NAMES}
    if not call_by_need:
        delivered["Thunk"] = _LazyThunk
    return delivered


def call_by_need_globals() -> dict:
    """The evaluation globals for a whole-program call-by-need module, derived from ``RUNTIME_API``:
    the unforced-cell sentinel its memo cells compare against, and ``node_case`` for a local analysis
    island that observes the source term it is applied to."""
    return {_SENTINEL_NAME: RUNTIME_API[_SENTINEL_NAME], "node_case": RUNTIME_API["node_case"]}


# A real import header so a generated interpret-headed module is self-contained and directly callable
# (``import``ed, or ``python -m``), rather than only runnable inside an ``interpret_globals`` namespace.
# Derived from RUNTIME_API: it binds exactly the interpret-headed names. ``Thunk`` defaults to the
# memoising ``_NeedThunk``; a loader may pre-bind ``Thunk`` in the exec namespace to override the lazy
# regime (``globals().get`` picks that up), which is how the benchmark measures call-by-name without
# changing the committed source. The header is added at serialization time, not by the COMPILE term.
_HEADER_AST_NAMES = tuple(name for name in _INTERPRET_HEADED_NAMES if name.startswith("make_"))
_HEADER_RUNTIME_NAMES = ("_NeedThunk", "force", "interpret", "value_island", "value_island_by_name")
_GENERATED_MODULE_HEADER = (
    "# Generated, self-contained module: the import header is added at serialization time (see\n"
    "# co_lambda._runtime.runnable_module); the body is emitted by the COMPILE lambda term.\n"
    "from co_lambda._ast import " + ", ".join(_HEADER_AST_NAMES) + "\n"
    "from co_lambda._runtime import (\n"
    + "".join(f"    {name},\n" for name in _HEADER_RUNTIME_NAMES)
    + ")\n"
    'Thunk = globals().get("Thunk", _NeedThunk)\n'
)


def runnable_module(anf_source: str) -> str:
    """Prepend the import header so an interpret-headed A-normal-form module runs on its own.

    The header binds the interpret-headed ``RUNTIME_API`` names, so ``import``ing the module (or
    ``python -m``) builds the node graph and binds ``compiled_compiler`` with no injected namespace.
    Building the graph is cheap: each island's read-back is deferred (a ``Native`` thunk), so
    importing does not run the islands."""
    return _GENERATED_MODULE_HEADER + "\n" + anf_source


# --- host stack headroom ---------------------------------------------------------------------------
# Building and decoding the generic Scott ast recurses about as deep as the term, so give the
# interpreter stack headroom above Python's default (the recursion is finite; raising the limit,
# restored after, is the fix, not a workaround).
_COMPILE_RECURSION_LIMIT = 16_000


@contextmanager
def recursion_headroom() -> "Iterator[None]":
    previous = sys.getrecursionlimit()
    sys.setrecursionlimit(max(previous, _COMPILE_RECURSION_LIMIT))
    try:
        yield
    finally:
        sys.setrecursionlimit(previous)


# A non-normalizing term runs a whole analysis fuel before the conservative verdict, so the
# interpreter's substitution recursion can be as deep as the fuel; that overflows the default C stack
# (a fatal crash setrecursionlimit cannot catch), so deep work runs inside a thread given a large C
# stack with a matching recursion limit, restored implicitly when the thread ends.
_RECURSION_LIMIT = 200_000
_STACK_SIZE = 1024 * 1024 * 1024  # 1 GiB


def run_in_large_stack(thunk):
    """Run ``thunk`` in a thread given a large C stack and a high recursion limit, returning its result.

    The lambda analyses drive the interpreter's substitution recursion as deep as their fuel, which
    overflows the default C stack (a fatal crash ``setrecursionlimit`` cannot catch); a thread with a
    large stack size and a matching recursion limit runs it safely, restored when the thread ends.
    """
    result: list = []

    def run() -> None:
        previous_limit = sys.getrecursionlimit()
        sys.setrecursionlimit(max(previous_limit, _RECURSION_LIMIT))
        try:
            result.append(thunk())
        finally:
            sys.setrecursionlimit(previous_limit)

    previous_stack_size = threading.stack_size(_STACK_SIZE)
    try:
        worker = threading.Thread(target=run)
        worker.start()
        worker.join()
    finally:
        threading.stack_size(previous_stack_size)
    single_result, = result
    return single_result
