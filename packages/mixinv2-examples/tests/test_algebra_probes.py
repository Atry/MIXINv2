"""Empirical probes for three further claim-audit repairs of the paper.

- P6 (expressive asymmetry, Appendix C): machine-checks the separating
  construction of thm:cartesian-nonexpressibility. The pair
  M = eq false false and N = eq true true (Church booleans,
  eq = \\a.\\b.(a b)(b false true)) both weak-head-reduce to true, yet the
  mixed context D[.] = (\\x. x Omega I) C[.] with the pure mixin context
  C[.] = {hole: [.], firstOperand: [[hole, __callee, __call, __parameter]],
  __whnf: [[firstOperand, __whnf]]} separates them: D[M] converges and D[N]
  diverges. A failure here indicts the theorem's construction: STOP.

- P7 (C/I/A of deep merge): on randomly generated small mixin documents,
  bounded-depth path existence is invariant under (i) permuting each node's
  reference list, (ii) duplicating references, and (iii) re-associating
  composition, where composition A (+) B is the wrapper mixin inheriting both
  bases. Outcomes are compared as values (either the path set or the
  exception class), so a crashing variant must crash identically. A failure
  refutes the paper's commutativity/idempotence/associativity claim: STOP.

- P8 (Levy-Longo readback): for enumerated and adversarial closed terms, a
  reference LLT computed by a budgeted lazy reducer is compared with the
  tree-side three-way observation readback: an abstraction shape (lambda
  node with its binder label), a chain ending finitely at a parameter
  declaration (head variable, arguments recovered from the redex thunks
  passed along the chain), or divergence (bottom). The chain is walked with
  the paper-faithful eq:bases steps.
"""

from __future__ import annotations

import json
import random
from pathlib import Path

import pytest

from mixinv2._core import MixinSymbol
from mixinv2._mixin_directory import DirectoryMixinDefinition

from test_lambda_adequacy_probes import (
    ADVERSARIAL_CONVERGING,
    DbApp,
    DbLam,
    DbTerm,
    DbVar,
    _convergence_verdict,
    _named,
    enumerate_closed_terms,
    krivine_halts,
    render,
    to_named,
    translate_named,
    weak_head_step,
)

# --- shared loading -------------------------------------------------------------


def load_raw_symbol(value, directory: Path) -> MixinSymbol:
    """Load an arbitrary mixin JSON value as Probe.mixin.json/term."""
    (directory / "Probe.mixin.json").write_text(json.dumps({"term": value}))
    definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=directory
    )
    root = MixinSymbol(origin=(definition,))
    return root["Probe"]["term"]


def _raw_convergence_verdict(value, directory: Path) -> bool:
    """Convergence of a raw mixin value, with the divergence handling of
    ``_convergence_verdict`` (repeating timer, recursion cap)."""
    import test_lambda_adequacy_probes as lam

    class _RawTerm:
        pass

    original = lam.load_translated_symbol
    lam.load_translated_symbol = lambda term, d: load_raw_symbol(value, d)
    try:
        return lam._convergence_verdict(_RawTerm(), directory)
    finally:
        lam.load_translated_symbol = original


# --- P6: the separating construction of Appendix C -------------------------------

TRUE_SRC = "L L 1"
FALSE_SRC = "L L 0"
IDENTITY_SRC = "L 0"
OMEGA_SRC = "A L A 0 0 L A 0 0"
EQ_SRC = f"L L A A 1 0 A A 0 {FALSE_SRC} {TRUE_SRC}"
M_SRC = f"A A {EQ_SRC} {FALSE_SRC} {FALSE_SRC}"
N_SRC = f"A A {EQ_SRC} {TRUE_SRC} {TRUE_SRC}"
DISCRIMINATOR_SRC = f"L A A 0 {OMEGA_SRC} {IDENTITY_SRC}"


def _context_c(hole_value) -> list:
    """C[.] of thm:cartesian-nonexpressibility, verbatim from the paper."""
    return [
        {"hole": hole_value},
        {"firstOperand": [["hole", "__callee", "__call", "__parameter"]]},
        {"__whnf": [["firstOperand", "__whnf"]]},
    ]


def _context_d(hole_value) -> list:
    """D[.] = (\\x. x Omega I) C[.]: the application rule of T with the
    parameter overridden by the raw mixin C[hole_value]."""
    discriminator = translate_named(to_named(_named(DISCRIMINATOR_SRC)))
    return [
        {"__callee": discriminator},
        {"__call": [["__callee", "__whnf"], {"__parameter": _context_c(hole_value)}]},
        {"__whnf": [["__call", "__result", "__whnf"]]},
    ]


def test_p6_pair_equivalent_in_lambda() -> None:
    """M and N both weak-head-reduce to Church true."""
    true_term = _named(TRUE_SRC)
    for source in (M_SRC, N_SRC):
        term = _named(source)
        assert krivine_halts(term, 500)
        for _ in range(500):
            step = weak_head_step(term)
            if step is None:
                break
            term = step
        assert term == true_term, (
            f"P6: {render(_named(source), 0)} reduced to {render(term, 0)},"
            " expected Church true"
        )


def test_p6_context_separates(tmp_path: Path) -> None:
    translated_m = translate_named(to_named(_named(M_SRC)))
    translated_n = translate_named(to_named(_named(N_SRC)))

    dm_directory = tmp_path / "dm"
    dm_directory.mkdir()
    dn_directory = tmp_path / "dn"
    dn_directory.mkdir()
    d_of_m = _raw_convergence_verdict(_context_d(translated_m), dm_directory)
    d_of_n = _raw_convergence_verdict(_context_d(translated_n), dn_directory)
    assert d_of_m, "P6 STOP: D[M] must converge (false Omega I -> I)"
    assert not d_of_n, "P6 STOP: D[N] must diverge (true Omega I -> Omega)"


# --- P7: C/I/A of deep merge ------------------------------------------------------

_LABELS = ("a", "b", "c", "d")
_P7_DEPTH = 6
_P7_SEEDS = tuple(range(12))


def _random_document(rng: random.Random, depth: int) -> list:
    """A random mixin value: a few property definitions and references."""
    items: list = []
    for label in _LABELS:
        if rng.random() < 0.6:
            if depth > 0 and rng.random() < 0.5:
                items.append({label: _random_document(rng, depth - 1)})
            else:
                items.append({label: []})
    reference_count = rng.randrange(0, 3)
    for _ in range(reference_count):
        length = rng.randrange(1, 3)
        items.append([rng.choice(_LABELS) for _ in range(length)])
    rng.shuffle(items)
    return items


def _permute_references(value, reverse: bool):
    if isinstance(value, dict):
        return {
            key: _permute_references(inner, reverse)
            for key, inner in value.items()
        }
    if isinstance(value, list) and value and all(
        isinstance(item, str) for item in value
    ):
        return value
    if isinstance(value, list):
        references = [
            item
            for item in value
            if isinstance(item, list)
        ]
        others = [
            _permute_references(item, reverse)
            for item in value
            if not isinstance(item, list)
        ]
        if reverse:
            references = list(reversed(references))
        return others + references
    return value


def _duplicate_references(value):
    if isinstance(value, dict):
        return {key: _duplicate_references(inner) for key, inner in value.items()}
    if isinstance(value, list) and value and all(
        isinstance(item, str) for item in value
    ):
        return value
    if isinstance(value, list):
        result = []
        for item in value:
            transformed = _duplicate_references(item)
            result.append(transformed)
            if isinstance(item, list):
                result.append(transformed)
        return result
    return value


def _observable_outcome(value, directory: Path):
    """Bounded-depth path-existence set, or the exception class name; the
    comparison across variants treats a crash as an observable outcome that
    must be reproduced identically by the transformed document."""
    import test_lambda_adequacy_probes as lam

    try:
        symbol = load_raw_symbol(value, directory)
        return frozenset(lam._existing_paths(symbol, _P7_DEPTH))
    except Exception as error:  # noqa: BLE001 -- outcome-as-value comparison
        return type(error).__name__


@pytest.mark.parametrize("seed", _P7_SEEDS)
def test_p7_reference_set_invariance(seed: int, tmp_path: Path) -> None:
    rng = random.Random(seed)
    document = _random_document(rng, 2)
    variants = {
        "original": document,
        "reversed": _permute_references(document, reverse=True),
        "duplicated": _duplicate_references(document),
    }
    outcomes = {}
    for name, variant in variants.items():
        directory = tmp_path / name
        directory.mkdir()
        outcomes[name] = _observable_outcome(variant, directory)
    assert outcomes["reversed"] == outcomes["original"], (
        f"P7 STOP (commutativity) seed={seed}: reference order changed the"
        f" observable outcome"
    )
    assert outcomes["duplicated"] == outcomes["original"], (
        f"P7 STOP (idempotence) seed={seed}: duplicating references changed"
        f" the observable outcome"
    )


def _association_outcomes(
    base_a: list, base_b: list, base_c: list, tmp_path: Path
) -> dict:
    """Bounded-depth existence outcomes of the three associations of the
    paper's five-wrapper construction (thm:merge-associative), with the
    wrappers nested under the reserved word __merge as in the theorem,
    compared as values (path set or exception class name)."""
    import test_lambda_adequacy_probes as lam

    def program(merged: list) -> list:
        return [
            {"BaseA": base_a},
            {"BaseB": base_b},
            {"BaseC": base_c},
            {
                "__merge": [
                    {"LeftPair": [["BaseA"], ["BaseB"]]},
                    {"RightPair": [["BaseB"], ["BaseC"]]},
                    {"merged": merged},
                ]
            },
        ]

    associations = {
        "left": [["LeftPair"], ["BaseC"]],
        "right": [["BaseA"], ["RightPair"]],
        "flat": [["BaseA"], ["BaseB"], ["BaseC"]],
    }
    outcomes = {}
    for name, merged in associations.items():
        directory = tmp_path / name
        directory.mkdir()
        try:
            symbol = load_raw_symbol(program(merged), directory)
            outcomes[name] = frozenset(
                lam._existing_paths(symbol["__merge"]["merged"], _P7_DEPTH)
            )
        except Exception as error:  # noqa: BLE001 -- outcome-as-value
            outcomes[name] = type(error).__name__
    return outcomes


@pytest.mark.parametrize("seed", _P7_SEEDS)
def test_p7_merge_associativity(seed: int, tmp_path: Path) -> None:
    rng = random.Random(seed + 1000)
    outcomes = _association_outcomes(
        _random_document(rng, 1),
        _random_document(rng, 1),
        _random_document(rng, 1),
        tmp_path,
    )
    assert outcomes["left"] == outcomes["flat"], (
        f"P7 STOP (associativity) seed={seed}: (A+B)+C differs from A+B+C:"
        f" {outcomes}"
    )
    assert outcomes["right"] == outcomes["flat"], (
        f"P7 STOP (associativity) seed={seed}: A+(B+C) differs from A+B+C:"
        f" {outcomes}"
    )


# --- P9: immunity to nonextensibility ----------------------------------------------

_P9_SEEDS = tuple(range(8))


def _grounded_document(rng: random.Random) -> list:
    """A random document whose lexical climbs always resolve: every probe
    label has a top-level fallback definition, and the random body sits
    under a nested label, so no written reference climbs past the root."""
    return [
        *({label: []} for label in _LABELS),
        {"inner": _random_document(rng, 2)},
    ]


@pytest.mark.parametrize("seed", _P9_SEEDS)
def test_p9_immunity_to_nonextensibility(seed: int, tmp_path: Path) -> None:
    """P9 (prop:immunity): composing any document with a reserved __extend
    wrapper (inheriting the document root and writing a nested definition
    chain along an arbitrary path, with a fresh __new leaf) makes the path
    p + (__new,) exist under the wrapper, while the document's own subtree
    is observationally unchanged."""
    import test_lambda_adequacy_probes as lam

    rng = random.Random(seed + 9000)
    base_p = _grounded_document(rng)
    alone_dir = tmp_path / "alone"
    alone_dir.mkdir()
    alone = load_raw_symbol([{"BaseP": base_p}], alone_dir)
    alone_paths = frozenset(lam._existing_paths(alone["BaseP"], _P7_DEPTH))

    existing = sorted(p for p in alone_paths if 0 < len(p) <= 3)
    candidate_paths = [()]
    if existing:
        candidate_paths.append(rng.choice(existing))
    candidate_paths.append(
        tuple(rng.choice(_LABELS) for _ in range(rng.randrange(1, 4)))
    )

    for index, path in enumerate(candidate_paths):
        directory = tmp_path / f"composite{index}"
        directory.mkdir()
        body: list = [{"__new": []}]
        for label in reversed(path):
            body = [{label: body}]
        composite = load_raw_symbol(
            [{"BaseP": base_p}, {"__extend": [["BaseP"], *body]}],
            directory,
        )
        extended_paths = lam._existing_paths(
            composite["__extend"], _P7_DEPTH
        )
        assert (*path, "__new") in extended_paths, (
            f"P9 STOP seed={seed}: extension {path} + ('__new',) missing"
            f" under __extend"
        )
        composed_base = frozenset(
            lam._existing_paths(composite["BaseP"], _P7_DEPTH)
        )
        assert composed_base == alone_paths, (
            f"P9 STOP seed={seed}: composing with __extend changed the base"
            f" document's observation"
        )
        preserved = {
            existing[len(path):]
            for existing in alone_paths
            if existing[: len(path)] == path
        }
        observed = {
            extended[len(path):]
            for extended in extended_paths
            if extended[: len(path)] == path
        }
        assert preserved <= observed, (
            f"P9 STOP seed={seed}: the wrapper does not preserve the base"
            f" observation at {path}: missing {preserved - observed}"
        )


_P7B_SOURCES = (
    ("identity_application", "A L 0 L 0"),
    ("k_on_identity", "A A L L 1 L 0 L 0"),
)


@pytest.mark.parametrize(("label", "source"), _P7B_SOURCES)
def test_p7b_merge_associativity_lambda_images(
    label: str, source: str, tmp_path: Path
) -> None:
    """Associativity with lambda-translation images among the bases: the
    application node of the translation carries the site-relative
    (de Bruijn index 0) reference [call, result, whnf], so chains from a
    merge root detour to suffixes deeper than the queried one --- exactly
    the shape that defeats a suffix-length induction. Bounded-depth
    existence must still agree across the three associations."""
    base_a = translate_named(to_named(_named(source)))
    base_b = translate_named(to_named(_named("L 0")))
    base_c = [{"extra": []}, ["extra"]]
    outcomes = _association_outcomes(base_a, base_b, base_c, tmp_path)
    assert outcomes["left"] == outcomes["flat"], (
        f"P7b STOP (associativity) [{label}]: (A+B)+C differs from A+B+C:"
        f" {outcomes}"
    )
    assert outcomes["right"] == outcomes["flat"], (
        f"P7b STOP (associativity) [{label}]: A+(B+C) differs from A+B+C:"
        f" {outcomes}"
    )


# --- P8: Levy-Longo readback -------------------------------------------------------
#
# The tree-side observation is computed by the OPEN Krivine machine with the
# configuration decoding of def:config-paths, extended with DECLARATION
# thunks: entering the body of an unapplied abstraction binds its variable to
# the shape instance's parameter declaration; looking up a declaration-bound
# variable blocks (a head variable), and the pending stack closures are its
# arguments. This is precisely the construction the Levy-Longo readback
# section of the paper formalizes; the probe validates it in lockstep against
# a reference LLT computed by a budgeted reducer.

_LLT_DEPTH = 3
_LLT_STEP_BUDGET = 300


def _reference_llt(term: DbTerm, depth: int):
    """Reference LLT to ``depth``: ("lam", body-llt) / ("var", level, args) /
    "bottom" / "cut". ``level`` counts binders from the OUTERMOST entered
    lambda (stable across the two sides). Works on open de Bruijn terms via
    environment-free substitution reduction."""

    def whnf(current: DbTerm) -> DbTerm | None:
        from test_lambda_adequacy_probes import substitute

        for _ in range(_LLT_STEP_BUDGET):
            if not isinstance(current, DbApp):
                return current
            spine: list[DbTerm] = []
            head: DbTerm = current
            while isinstance(head, DbApp):
                spine.append(head.operand)
                head = head.operator
            if isinstance(head, DbVar):
                return current
            spine.reverse()
            first_argument, *rest = spine
            assert isinstance(head, DbLam)
            contracted = substitute(head.body, 0, first_argument)
            for argument in rest:
                contracted = DbApp(operator=contracted, operand=argument)
            current = contracted
        return None

    def recurse(current: DbTerm, binder_depth: int, remaining: int):
        if remaining == 0:
            return "cut"
        normal = whnf(current)
        if normal is None:
            return "bottom"
        if isinstance(normal, DbLam):
            return (
                "lam",
                recurse(normal.body, binder_depth + 1, remaining - 1),
            )
        spine: list[DbTerm] = []
        head: DbTerm = normal
        while isinstance(head, DbApp):
            spine.append(head.operand)
            head = head.operator
        assert isinstance(head, DbVar)
        spine.reverse()
        level = binder_depth - 1 - head.index
        return (
            "var",
            level,
            tuple(
                recurse(argument, binder_depth, remaining - 1)
                for argument in spine
            ),
        )

    return recurse(term, 0, depth)


def _tree_llt(root: MixinSymbol, term: DbTerm, focus: tuple, depth: int):
    """Tree-side LLT readback by the open decoded machine.

    A machine state is (control, env, stack, focus): env entries are either
    ("thunk", term, env, path) or ("decl", level, path); stack entries are
    ("thunk", term, env, path). The declaration paths are corroborated
    against the tree at every lookup of a declaration-bound variable.
    """
    import test_lambda_adequacy_probes as lam

    def run(control: DbTerm, environment: tuple, stack: tuple,
            position: tuple, binder_depth: int, remaining: int):
        if remaining == 0:
            return "cut"
        for _ in range(_LLT_STEP_BUDGET):
            if isinstance(control, DbApp):
                closure = ("thunk", control.operand, environment,
                           (*position, "__call", "__parameter"))
                stack = (closure, *stack)
                control = control.operator
                position = (*position, "__callee")
            elif isinstance(control, DbLam):
                if stack:
                    closure, *rest = stack
                    stack = tuple(rest)
                    thunk_path = closure[3]
                    assert thunk_path[-2:] == ("__call", "__parameter"), (
                        f"P8: malformed thunk path {thunk_path}"
                    )
                    environment = (closure, *environment)
                    position = (*thunk_path[:-1], "__result")
                    control = control.body
                else:
                    shape = (*position, "__whnf")
                    symbol = lam._sym_at(root, shape)
                    assert symbol is not None, (
                        f"P8: abstraction shape missing at {shape}"
                    )
                    keys = set(symbol)
                    assert "__parameter" in keys and "__result" in keys, (
                        f"P8: {shape} is not an abstraction shape"
                        f" (keys {sorted(map(str, keys))})"
                    )
                    declaration = ("decl", binder_depth, (*shape, "__parameter"))
                    body = run(
                        control.body,
                        (declaration, *environment),
                        (),
                        (*shape, "__result"),
                        binder_depth + 1,
                        remaining - 1,
                    )
                    return ("lam", body)
            else:
                entry = environment[control.index]
                if entry[0] == "thunk":
                    _, entry_term, entry_env, entry_path = entry
                    control = entry_term
                    environment = entry_env
                    position = entry_path
                else:
                    _, level, declaration_path = entry
                    variable_targets = lam._paper_bases_targets(
                        root, position
                    )
                    assert variable_targets is not None and len(
                        variable_targets
                    ) == 1, (
                        f"P8: head variable at {position} resolved to"
                        f" {variable_targets}"
                    )
                    alias_position, = variable_targets
                    alias_targets = lam._paper_bases_targets(
                        root, alias_position
                    )
                    assert alias_targets is not None and len(
                        alias_targets
                    ) == 1, (
                        f"P8: alias at {alias_position} resolved to"
                        f" {alias_targets}"
                    )
                    resolved_declaration, = alias_targets
                    assert tuple(resolved_declaration) == tuple(
                        declaration_path
                    ), (
                        f"P8: head variable forwarded to"
                        f" {resolved_declaration}, expected declaration"
                        f" {declaration_path}"
                    )
                    return (
                        "var",
                        level,
                        tuple(
                            run(argument_term, argument_env, (),
                                argument_path, binder_depth, remaining - 1)
                            for (_, argument_term, argument_env,
                                 argument_path) in stack
                        ),
                    )
        return "bottom"

    return run(term, (), (), focus, 0, depth)


@pytest.mark.parametrize(
    ("label", "source"),
    (
        ("identity", "L 0"),
        ("k_combinator", "L L 1"),
        ("open_body", "L A 0 L 0"),
        ("var_head_args", "L A A 0 L 0 L L 1"),
        ("nested", "A L L A 1 0 L 0"),
        ("omega_under_lambda", "L A L A 0 0 L A 0 0"),
    )
    + ADVERSARIAL_CONVERGING,
)
def test_p8_llt_readback(label: str, source: str, tmp_path: Path) -> None:
    term = _named(source)
    reference = _reference_llt(term, _LLT_DEPTH)
    named = to_named(term)
    (tmp_path / "Probe.mixin.json").write_text(
        json.dumps({"term": translate_named(named)})
    )
    definition = DirectoryMixinDefinition(
        inherits=(), is_public=True, underlying=tmp_path
    )
    root = MixinSymbol(origin=(definition,))
    observed = _tree_llt(root, term, ("Probe", "term"), _LLT_DEPTH)
    assert observed == reference, (
        f"P8 MISMATCH [{label}]: tree readback {observed} != reference LLT"
        f" {reference}"
    )
