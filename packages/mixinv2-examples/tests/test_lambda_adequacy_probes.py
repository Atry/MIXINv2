"""Empirical probes for the adequacy proof chain of the inheritance-calculus paper.

These tests validate, on the interpreter, the lemma statements that the
rewritten Appendix B will prove, BEFORE any LaTeX is written:

- P1 (kernel, go/no-go for the whole repair): for images of closed lambda-terms
  under the paper's translation T, resolution never branches ON THE DEMANDED
  CONE OF A CONVERGING PROGRAM. Concretely, for converging terms: every
  ``qualified_this`` mapping recorded during the convergence query assigns at
  most one inheritance site per override (functionality of ``supers`` in its
  override component, lemma ``supers-functional``), every paper-faithful
  ``bases`` value has at most one element, and every ``this`` frontier stays
  at most a singleton (lemma ``single-path``). The GLOBAL functionality
  statement is FALSE and known to be false: on Omega, one chain incorporates
  the same definition-site override at two depths (a reduction loop revisits
  the same code), and a converging program containing a diverging subtree
  (e.g. (lambda x. lambda y. y) Omega I) inherits those out-of-cone
  violations, so the repaired Appendix B lemmas quantify over the demanded
  cone only (author decision). Diverging terms therefore run in MONITOR mode
  here: functionality violations are expected and recorded, and frontier
  violations merely warn (empirically the frontier stays <= 1 even on Omega's
  8114 this-steps, which exceeds what the lemma promises).
- P2 (the bridge of the machine-simulation architecture): the call-by-name
  Krivine machine halts on M if and only if T(M) converges
  (``supers(("__whnf","__parameter")) != empty`` per def:convergence).
- P3: the paths existing under the reduct position ("__call","__result") of
  T((lambda x.M) V) coincide with the paths existing at the root of
  T(M[V/x]), up to a depth bound (the old substitution lemma's content,
  retained as an empirical check even though the repaired proof no longer
  states it).
- P4: convergence is preserved and reflected across one weak-head step.
- P5 (laziness feasibility record): the encoding is NOT fully lazy in the
  fact-counting cost model; the body of a shared abstraction is replayed at
  each call site's path family.

Divergence handling: a diverging query has no answer in the implementation
either; it manifests as ``FixpointRecursionError``, ``RecursionError``, or a
wall-clock timeout. The single helper ``_convergence_verdict`` catches exactly
these three as the expected "no answer" signals of the semantics (this is not
error recovery; a crash of any other kind propagates).
"""

from __future__ import annotations

import json
import signal
import sys
import warnings
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import final

import pytest

import _trace_patch
from mixinv2 import FixpointRecursionError
from mixinv2._core import MixinSymbol
from mixinv2._mixin_directory import DirectoryMixinDefinition


# --- de Bruijn lambda-terms ---------------------------------------------------


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class DbVar:
    index: int


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class DbLam:
    body: "DbTerm"


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class DbApp:
    operator: "DbTerm"
    operand: "DbTerm"


DbTerm = DbVar | DbLam | DbApp


def render(term: DbTerm, depth: int) -> str:
    if isinstance(term, DbVar):
        return f"v{depth - 1 - term.index}"
    if isinstance(term, DbLam):
        return f"(\\v{depth}. {render(term.body, depth + 1)})"
    return f"({render(term.operator, depth)} {render(term.operand, depth)})"


def enumerate_closed_terms(max_size: int) -> tuple[DbTerm, ...]:
    """All closed de Bruijn terms with at most ``max_size`` AST nodes."""

    def terms_of(size: int, depth: int) -> Iterator[DbTerm]:
        if size <= 0:
            return
        if size == 1:
            for index in range(depth):
                yield DbVar(index=index)
            return
        for body in terms_of(size - 1, depth + 1):
            yield DbLam(body=body)
        for operator_size in range(1, size - 1):
            for operator in terms_of(operator_size, depth):
                for operand in terms_of(size - 1 - operator_size, depth):
                    yield DbApp(operator=operator, operand=operand)

    collected: list[DbTerm] = []
    for size in range(1, max_size + 1):
        collected.extend(terms_of(size, 0))
    assert collected, "term enumeration must be non-empty"
    return tuple(collected)


# --- weak-head reduction (de Bruijn, capture-free by construction) ------------


def shift(term: DbTerm, amount: int, cutoff: int) -> DbTerm:
    if isinstance(term, DbVar):
        if term.index >= cutoff:
            shifted = term.index + amount
            assert shifted >= 0, "negative de Bruijn index after shift"
            return DbVar(index=shifted)
        return term
    if isinstance(term, DbLam):
        return DbLam(body=shift(term.body, amount, cutoff + 1))
    return DbApp(
        operator=shift(term.operator, amount, cutoff),
        operand=shift(term.operand, amount, cutoff),
    )


def substitute(term: DbTerm, target_index: int, replacement: DbTerm) -> DbTerm:
    if isinstance(term, DbVar):
        if term.index == target_index:
            return shift(replacement, target_index, 0)
        if term.index > target_index:
            return DbVar(index=term.index - 1)
        return term
    if isinstance(term, DbLam):
        return DbLam(
            body=substitute(term.body, target_index + 1, replacement)
        )
    return DbApp(
        operator=substitute(term.operator, target_index, replacement),
        operand=substitute(term.operand, target_index, replacement),
    )


def weak_head_step(term: DbTerm) -> DbTerm | None:
    """One weak-head reduction step of a closed term, or None at WHNF."""
    if not isinstance(term, DbApp):
        return None
    spine: list[DbTerm] = []
    head: DbTerm = term
    while isinstance(head, DbApp):
        spine.append(head.operand)
        head = head.operator
    assert not isinstance(head, DbVar), "closed term cannot have a variable head"
    spine.reverse()
    first_argument, *rest = spine
    assert isinstance(head, DbLam)
    contracted = substitute(head.body, 0, first_argument)
    for argument in rest:
        contracted = DbApp(operator=contracted, operand=argument)
    return contracted


# --- call-by-name Krivine machine ---------------------------------------------


def krivine_halts(term: DbTerm, max_steps: int) -> bool:
    """Run the call-by-name Krivine machine; True iff it halts within budget."""
    control: DbTerm = term
    environment: tuple = ()
    stack: tuple = ()
    for _ in range(max_steps):
        if isinstance(control, DbLam):
            if not stack:
                return True
            closure, *stack_rest = stack
            stack = tuple(stack_rest)
            environment = (closure, *environment)
            control = control.body
        elif isinstance(control, DbApp):
            stack = ((control.operand, environment), *stack)
            control = control.operator
        else:
            control, environment = environment[control.index]
    return False


# --- the paper's translation T, emitted as .mixin.json ------------------------


def translate(term: DbTerm, depth: int) -> list:
    """The paper's T (Section 4): variable / abstraction / application rules."""
    if isinstance(term, DbVar):
        return [[f"v{depth - 1 - term.index}"]]
    if isinstance(term, DbLam):
        return [
            {
                "__whnf": [
                    {f"v{depth}": [["__parameter"]]},
                    {"__parameter": []},
                    {"__result": translate(term.body, depth + 1)},
                ]
            }
        ]
    return [
        {"__callee": translate(term.operator, depth)},
        {
            "__call": [
                ["__callee", "__whnf"],
                {"__parameter": translate(term.operand, depth)},
            ]
        },
        {"__whnf": [["__call", "__result", "__whnf"]]},
    ]


def load_translated_symbol(term: DbTerm, directory: Path) -> MixinSymbol:
    """Write T(term) as Probe.mixin.json under ``directory`` and load it."""
    program = {"term": translate(term, 0)}
    (directory / "Probe.mixin.json").write_text(json.dumps(program))
    definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=directory
    )
    root = MixinSymbol(origin=(definition,))
    return root["Probe"]["term"]


# --- named terms (binder identity carries the name, so substitution does not
# --- rename and both sides of P3 translate with identical alias labels) --------


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class NamedVar:
    name: str


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class NamedLam:
    name: str
    body: "NamedTerm"


@final
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class NamedApp:
    operator: "NamedTerm"
    operand: "NamedTerm"


NamedTerm = NamedVar | NamedLam | NamedApp


def to_named(term: DbTerm) -> NamedTerm:
    """Assign a globally unique name to every binder, once; substitution then
    never captures or renames (arguments of head redexes are closed)."""
    counter = [0]

    def convert(current: DbTerm, binders: tuple[str, ...]) -> NamedTerm:
        if isinstance(current, DbVar):
            return NamedVar(name=binders[current.index])
        if isinstance(current, DbLam):
            name = f"v{counter[0]}"
            counter[0] += 1
            return NamedLam(
                name=name, body=convert(current.body, (name, *binders))
            )
        return NamedApp(
            operator=convert(current.operator, binders),
            operand=convert(current.operand, binders),
        )

    return convert(term, ())


def substitute_named(
    term: NamedTerm, name: str, replacement: NamedTerm
) -> NamedTerm:
    if isinstance(term, NamedVar):
        return replacement if term.name == name else term
    if isinstance(term, NamedLam):
        assert term.name != name, "binder names are globally unique"
        return NamedLam(
            name=term.name,
            body=substitute_named(term.body, name, replacement),
        )
    return NamedApp(
        operator=substitute_named(term.operator, name, replacement),
        operand=substitute_named(term.operand, name, replacement),
    )


def translate_named(term: NamedTerm) -> list:
    if isinstance(term, NamedVar):
        return [[term.name]]
    if isinstance(term, NamedLam):
        return [
            {
                "__whnf": [
                    {term.name: [["__parameter"]]},
                    {"__parameter": []},
                    {"__result": translate_named(term.body)},
                ]
            }
        ]
    return [
        {"__callee": translate_named(term.operator)},
        {
            "__call": [
                ["__callee", "__whnf"],
                {"__parameter": translate_named(term.operand)},
            ]
        },
        {"__whnf": [["__call", "__result", "__whnf"]]},
    ]


def load_named_symbol(term: NamedTerm, directory: Path) -> MixinSymbol:
    program = {"term": translate_named(term)}
    (directory / "Probe.mixin.json").write_text(json.dumps(program))
    definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=directory
    )
    root = MixinSymbol(origin=(definition,))
    return root["Probe"]["term"]


# --- divergence-aware convergence check ----------------------------------------


@final
class _ProbeTimeout(Exception):
    pass


def _alarm_handler(signum, frame) -> None:
    raise _ProbeTimeout()


_TIMEOUT_SECONDS = 10
_RECURSION_LIMIT = 8_000


def _convergence_verdict(term: DbTerm, directory: Path) -> bool:
    """True iff T(term) converges: supers(("__whnf","__parameter")) != empty.

    FixpointRecursionError / RecursionError / timeout are the implementation's
    three faces of "the demanded cone is infinite", i.e. divergence. The timer
    REPEATS (setitimer with an interval) because intermediate machinery may
    swallow one injected exception and retry; a repeating timer guarantees the
    next tick interrupts the retry as well.
    """
    previous_limit = sys.getrecursionlimit()
    previous_handler = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.setitimer(
        signal.ITIMER_REAL, _TIMEOUT_SECONDS, _TIMEOUT_SECONDS
    )
    sys.setrecursionlimit(_RECURSION_LIMIT)
    try:
        symbol = load_translated_symbol(term, directory)
        return "__parameter" in symbol["__whnf"]
    except (FixpointRecursionError, RecursionError, _ProbeTimeout):
        return False
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0, 0)
        signal.signal(signal.SIGALRM, previous_handler)
        sys.setrecursionlimit(previous_limit)


# --- shared term families -------------------------------------------------------


def _named(source: str) -> DbTerm:
    """Tiny reference-free builder for the adversarial terms, from strings.

    Grammar (whitespace-separated, prefix): ``L <body>`` for lambda,
    ``A <operator> <operand>`` for application, ``<int>`` for a de Bruijn var.
    """
    tokens = source.split()

    def parse(position: int) -> tuple[DbTerm, int]:
        token = tokens[position]
        if token == "L":
            body, next_position = parse(position + 1)
            return DbLam(body=body), next_position
        if token == "A":
            operator, after_operator = parse(position + 1)
            operand, after_operand = parse(after_operator)
            return DbApp(operator=operator, operand=operand), after_operand
        return DbVar(index=int(token)), position + 1

    term, consumed = parse(0)
    assert consumed == len(tokens), f"trailing tokens in {source!r}"
    return term


IDENTITY = "L 0"
ADVERSARIAL_CONVERGING: tuple[tuple[str, str], ...] = (
    # (lambda f. f (f I)) (lambda y. y): one abstraction incorporated at two
    # call sites -- the multi-incorporation shape for supers functionality.
    ("shared_abstraction", f"A L A 0 A 0 {IDENTITY} {IDENTITY}"),
    # (lambda f. f (f I)) (lambda y. lambda w. y): forces an n>=1 this-climb
    # inside a twice-incorporated abstraction.
    ("shared_two_level", f"A L A 0 A 0 {IDENTITY} L L 1"),
    # ((lambda x. lambda w. x) I) I: nested redexes, ((lambda x.M) V) W.
    ("nested_redex", f"A A L L 1 {IDENTITY} {IDENTITY}"),
    # twice twice I with twice = lambda f. lambda x. f (f x).
    ("twice_twice", f"A A L L A 1 A 1 0 L L A 1 A 1 0 {IDENTITY}"),
    # rebinding: (lambda x. (lambda y. y I) x) (lambda z. I): the argument is
    # forced through a second binder.
    ("rebinding", f"A L A L A 0 {IDENTITY} 0 L {IDENTITY}"),
)
ADVERSARIAL_DIVERGING: tuple[tuple[str, str], ...] = (
    ("omega", "A L A 0 0 L A 0 0"),
    ("omega3", "A L A 0 0 L A A 0 0 0"),
    # (lambda y. (lambda x. x x) (lambda z. (z z) y)) I: a deep-climb monitor,
    # the variable y climbs out of a shape that the diverging chain re-enters.
    ("deep_climb", "A L A L A 0 0 L A A 0 0 1 L 0"),
)

ENUMERATED = enumerate_closed_terms(6)
KRIVINE_BUDGET = 500


# --- P1: supers functionality, |bases| <= 1, singleton frontiers ---------------


def _sym_at(root_symbol: MixinSymbol, full_path: tuple):
    symbol = root_symbol
    for key in full_path:
        symbol = symbol.get(key)
        if symbol is None:
            return None
    return symbol


def _paper_bases_targets(root_symbol: MixinSymbol, full_path: tuple):
    """The paper's eq:bases at ``full_path``: resolve every reference of every
    override at the enclosing scope. Unlike ``ResolvedReference.get_symbols``,
    targets are computed as PATH TUPLES without navigating symbols: eq:resolve
    returns paths, and a returned path may simply not exist (its supers is
    empty downstream); navigation would crash on such a target."""
    path_symbol = _sym_at(root_symbol, full_path)
    site = _sym_at(root_symbol, full_path[:-1])
    if path_symbol is None or site is None:
        return None
    targets = []
    try:
        overrides = tuple(path_symbol.overrides)
        for override in overrides:
            for reference in override.normalized_references:
                frontier = (site,)
                definition_site = reference.origin_symbol
                for _ in range(reference.de_bruijn_index):
                    frontier = tuple(
                        next_site
                        for current in frontier
                        for next_site in current.qualified_this.get(
                            definition_site, ()
                        )
                    )
                    definition_site = definition_site.outer
                for current in frontier:
                    rendered = (*current.path, *reference.path)
                    if rendered not in targets:
                        targets.append(rendered)
    except ValueError:
        # Forcing overrides/references at a definition-site copy outside the
        # demanded cone makes the interpreter's eager navigation crash (e.g.
        # a variable's alias forwards to the EMPTY parameter declaration at
        # the definition site, so [callee, whnf] has no target there). The
        # kernel lemma quantifies over the demanded cone only, so such
        # positions are out of scope for this probe; skip them.
        return None
    return targets


def _scan_p1_records(label: str, strict: bool) -> None:
    """Assert P1 invariants over everything the trace recorded.

    ``strict=True`` (converging term: the trace IS the demanded cone of the
    convergence query) asserts both functionality and frontier <= 1.
    ``strict=False`` (diverging term: the recorded prefix is out-of-cone)
    monitors only: functionality violations are the documented out-of-cone
    behavior (a reduction loop revisits the same override on one chain), and
    a frontier violation, never yet observed even on Omega, warns instead of
    failing because the repaired lemma promises nothing outside the cone."""
    for record in _trace_patch.RECORDS:
        if record["function"] == "supers":
            if not strict:
                continue
            sites_of: dict = {}
            for site, override in record["pairs"]:
                sites_of.setdefault(override, set()).add(site)
            for override, sites in sites_of.items():
                assert len(sites) <= 1, (
                    f"P1 FUNCTIONALITY VIOLATION [{label}]: supers"
                    f"({record['path']}) maps override {override} to"
                    f" {len(sites)} sites: {sorted(sites)}"
                )
        elif record["function"] == "this":
            frontier_size = max(
                len(record["frontier_in"]), len(record["frontier_out"])
            )
            if frontier_size <= 1:
                continue
            message = (
                f"P1 FRONTIER VIOLATION [{label}]: this at def_site"
                f" {record['def_site']}: {record['frontier_in']} ->"
                f" {record['frontier_out']}"
            )
            assert not strict, message
            warnings.warn(message, stacklevel=2)


def _run_traced_convergence(term: DbTerm, directory: Path) -> bool:
    _trace_patch.reset()
    _trace_patch.install()
    _trace_patch.ENABLED = True
    try:
        return _convergence_verdict(term, directory)
    finally:
        _trace_patch.ENABLED = False
        _trace_patch.uninstall()


@pytest.mark.parametrize(("label", "source"), ADVERSARIAL_CONVERGING)
def test_p1_adversarial_converging(
    label: str, source: str, tmp_path: Path
) -> None:
    term = _named(source)
    converged = _run_traced_convergence(term, tmp_path)
    assert converged, f"adversarial converging term diverged: {label}"
    _scan_p1_records(label, strict=True)


@pytest.mark.parametrize(("label", "source"), ADVERSARIAL_DIVERGING)
def test_p1_adversarial_diverging_monitor(
    label: str, source: str, tmp_path: Path
) -> None:
    term = _named(source)
    converged = _run_traced_convergence(term, tmp_path)
    assert not converged, f"adversarial diverging term converged: {label}"
    _scan_p1_records(label, strict=False)


def test_p1_enumerated(tmp_path: Path) -> None:
    for position, term in enumerate(ENUMERATED):
        directory = tmp_path / str(position)
        directory.mkdir()
        converged = _run_traced_convergence(term, directory)
        _scan_p1_records(render(term, 0), strict=converged)


@pytest.mark.parametrize(("label", "source"), ADVERSARIAL_CONVERGING)
def test_p1_paper_bases_at_most_one(
    label: str, source: str, tmp_path: Path
) -> None:
    """Paper-faithful eq:bases has at most one target at every demanded path."""
    term = _named(source)
    converged = _run_traced_convergence(term, tmp_path)
    assert converged, f"adversarial converging term diverged: {label}"
    visited_paths = {
        tuple(record["path"])
        for record in _trace_patch.RECORDS
        if record["function"] in ("supers", "overrides") and record["path"]
    }
    definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=tmp_path
    )
    root = MixinSymbol(origin=(definition,))
    for full_path in sorted(visited_paths):
        targets = _paper_bases_targets(root, full_path)
        if targets is None:
            continue
        assert len(targets) <= 1, (
            f"P1 BASES VIOLATION [{label}]: eq:bases({full_path}) ="
            f" {targets}"
        )


# --- P2: Krivine machine halts iff the tree converges ---------------------------


@pytest.mark.parametrize(
    ("label", "source"), ADVERSARIAL_CONVERGING + ADVERSARIAL_DIVERGING
)
def test_p2_adversarial(label: str, source: str, tmp_path: Path) -> None:
    term = _named(source)
    machine = krivine_halts(term, KRIVINE_BUDGET)
    tree = _convergence_verdict(term, tmp_path)
    assert machine == tree, (
        f"P2 MISMATCH [{label}]: machine halts={machine}, tree"
        f" converges={tree}"
    )


def test_p2_enumerated(tmp_path: Path) -> None:
    for position, term in enumerate(ENUMERATED):
        directory = tmp_path / str(position)
        directory.mkdir()
        machine = krivine_halts(term, KRIVINE_BUDGET)
        tree = _convergence_verdict(term, directory)
        assert machine == tree, (
            f"P2 MISMATCH [{render(term, 0)}]: machine halts={machine},"
            f" tree converges={tree}"
        )


# --- P3: reduct-position paths match the contractum's program -------------------


_P3_DEPTH = 8


def _existing_paths(symbol: MixinSymbol, depth: int) -> set:
    """All existing paths under ``symbol`` up to ``depth``, by key iteration."""
    if depth == 0:
        return {()}
    paths = {()}
    for key in symbol:
        for suffix in _existing_paths(symbol[key], depth - 1):
            paths.add((key, *suffix))
    return paths


def _beta_redexes() -> tuple[tuple[str, DbTerm], ...]:
    """Closed beta-redexes (lambda x. M) V from the enumeration + adversaries."""
    redexes: list[tuple[str, DbTerm]] = []
    for term in ENUMERATED:
        if (
            isinstance(term, DbApp)
            and isinstance(term.operator, DbLam)
            and krivine_halts(term, KRIVINE_BUDGET)
        ):
            redexes.append((render(term, 0), term))
    for label, source in ADVERSARIAL_CONVERGING:
        term = _named(source)
        if isinstance(term, DbApp) and isinstance(term.operator, DbLam):
            redexes.append((label, term))
    assert redexes, "no beta-redexes found for P3"
    return tuple(redexes)


def test_p3_reduct_paths(tmp_path: Path) -> None:
    for position, (label, db_redex) in enumerate(_beta_redexes()):
        redex = to_named(db_redex)
        assert isinstance(redex, NamedApp)
        operator = redex.operator
        assert isinstance(operator, NamedLam)
        contractum = substitute_named(
            operator.body, operator.name, redex.operand
        )

        redex_directory = tmp_path / f"redex{position}"
        redex_directory.mkdir()
        redex_symbol = load_named_symbol(redex, redex_directory)
        reduct_position_symbol = redex_symbol["__call"]["__result"]

        contractum_directory = tmp_path / f"contractum{position}"
        contractum_directory.mkdir()
        contractum_symbol = load_named_symbol(
            contractum, contractum_directory
        )

        left = _existing_paths(reduct_position_symbol, _P3_DEPTH)
        right = _existing_paths(contractum_symbol, _P3_DEPTH)
        assert left == right, (
            f"P3 MISMATCH [{label}]: only under (call,result):"
            f" {sorted(left - right)}; only in contractum:"
            f" {sorted(right - left)}"
        )


# --- P4: convergence preserved and reflected across one weak-head step ----------


def test_p4_weak_head_step(tmp_path: Path) -> None:
    checked = 0
    for position, term in enumerate(ENUMERATED):
        reduct = weak_head_step(term)
        if reduct is None:
            continue
        before_directory = tmp_path / f"before{position}"
        before_directory.mkdir()
        after_directory = tmp_path / f"after{position}"
        after_directory.mkdir()
        before = _convergence_verdict(term, before_directory)
        after = _convergence_verdict(reduct, after_directory)
        assert before == after, (
            f"P4 MISMATCH [{render(term, 0)} ->h {render(reduct, 0)}]:"
            f" before={before}, after={after}"
        )
        checked += 1
    assert checked > 0, "P4 exercised no weak-head steps"


# --- P5: the encoding is not fully lazy (fact-counting record) -------------------


def test_p5_body_replayed_per_call_site(tmp_path: Path) -> None:
    """The shared abstraction's body chain is re-derived at each call site:
    the demanded cone contains supers facts at BOTH call-site path families,
    so the encoding is not fully lazy in the fact-counting model."""
    label, source = ADVERSARIAL_CONVERGING[0]
    term = _named(source)
    converged = _run_traced_convergence(term, tmp_path)
    assert converged, f"{label} must converge"
    supers_paths = [
        tuple(record["path"])
        for record in _trace_patch.RECORDS
        if record["function"] == "supers"
    ]
    outer_call_facts = [
        path for path in supers_paths if path[:2] == ("Probe", "term")
        and "__call" in path[2:]
    ]
    assert outer_call_facts, "no call-site supers facts recorded"
    call_prefixes = {
        path[: path.index("__call") + 1]
        for path in (p[2:] for p in outer_call_facts)
        if "__call" in path
    }
    assert len(call_prefixes) >= 2, (
        "expected supers facts at two or more distinct call-site path"
        f" families (per-site replay), got prefixes: {sorted(call_prefixes)}"
    )
