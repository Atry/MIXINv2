"""Demo encoders and built example nodes (boundary test data, not compiler source).

Holds the example material split out of the pure-lambda ``_prelude``: built (interned) example
``Node``s, node-level assembly helpers whose point is interning-aware sharing, and the demo
ENCODERS that mechanically encode a Python problem description (a ground Datalog program, a tree
shape) into a lambda term. The encoders are codecs in the register's sense (their non-Builder
parameters are the data being encoded); they live here rather than in ``_codec`` because they are
demonstration harnesses, not part of the compiler's input/output path.
"""

from __future__ import annotations

from co_lambda._ast import Node, make_app
from co_lambda._codec import church
from co_lambda._dsl import Builder, app, build, lam
from co_lambda._imperative import GEN
from co_lambda._pyast import _church_to_int, _extract
from co_lambda._prelude import (
    AND,
    FALSE,
    GAME_LEAF,
    IDENTITY,
    KESTREL,
    MAX_NODE,
    MIN_NODE,
    MINIMAX,
    OR,
    SCOTT_CONS,
    SCOTT_NIL,
    SELF_APPLY,
    TREE_ANY,
    TREE_LEAF,
    TREE_NODE,
    TRUE,
    Y,
    ZERO,
)

# Example terms (built de Bruijn nodes). The calculus is pure: cyclic and recursive data
# are written with Y, and interning folds the structurally-repeating positions.
IDENTITY_TERM: Node = build(IDENTITY)
KESTREL_TERM: Node = build(KESTREL)
OMEGA: Node = build(app(SELF_APPLY, SELF_APPLY))  # an unproductive cycle
FINITE_LIST: Node = build(app(app(SCOTT_CONS, ZERO), SCOTT_NIL))  # cons 0 nil

# r = cons 0 r : the cyclic stream, written Y (cons 0) (no recursion binder needed).
CYCLIC_ZEROS: Node = build(app(Y, app(SCOTT_CONS, ZERO)))

# letrec x = x : an unproductive head cycle, written Y (lambda x. x).
LOOP: Node = build(app(Y, IDENTITY))


# =====================================================================
# Pure Datalog as a monotone Church-boolean least fixpoint (a demo ENCODER).
#
# A ground Datalog program (no function symbols, so a finite Herbrand base) is a monotone
# Boolean equation system over its ground atoms. A model is a Church tuple of booleans; the
# immediate-consequence operator T_P is a tuple-to-tuple function; the least Herbrand model is
# T_P iterated |HB| times from the all-false tuple. A goal atom is a projection.
# =====================================================================


def _tuple(elements: "list[Builder]") -> Builder:
    # <e0, ..., e_{n-1}> = lambda s. s e0 ... e_{n-1}
    def apply_all(selector: Builder) -> Builder:
        applied = selector
        for element in elements:
            applied = app(applied, element)
        return applied

    return lam(apply_all)


def _select(index: int, arity: int) -> Builder:
    # lambda x0 ... x_{arity-1}. x_index
    def make(captured: "list[Builder]") -> Builder:
        if len(captured) == arity:
            return captured[index]
        return lam(lambda variable: make(captured + [variable]))

    return make([])


def _proj(index: int, arity: int) -> Builder:
    # pi_index = lambda t. t (select index arity)
    return lam(lambda the_tuple: app(the_tuple, _select(index, arity)))


def _conjunction(body, num_atoms: int, model: Builder) -> Builder:
    # AND over the body atoms of their current truth; an empty body (a fact) is TRUE.
    if not body:
        return TRUE
    first, *rest = body
    conjunction = app(_proj(first, num_atoms), model)
    for atom in rest:
        conjunction = app(app(AND, conjunction), app(_proj(atom, num_atoms), model))
    return conjunction


def _disjunction(clause_truths: "list[Builder]") -> Builder:
    # OR over the clauses deriving an atom; no clause is FALSE.
    if not clause_truths:
        return FALSE
    first, *rest = clause_truths
    disjunction = first
    for clause in rest:
        disjunction = app(app(OR, disjunction), clause)
    return disjunction


def datalog_model(num_atoms: int, clauses) -> Builder:
    """The least Herbrand model of a ground program, as a Church tuple of booleans.

    ``clauses`` is a sequence of ``(head, body)`` with 0-based atom indices; a fact has an empty
    ``body``. Returns the least fixpoint of ``T_P``, computed as ``T_P`` iterated ``num_atoms``
    times from the all-false tuple (the lattice has height ``num_atoms``, so this reaches it).
    """
    def step(model: Builder) -> Builder:
        cells = [
            _disjunction(
                [_conjunction(body, num_atoms, model)
                 for (head, body) in clauses if head == atom]
            )
            for atom in range(num_atoms)
        ]
        return _tuple(cells)

    bottom = _tuple([FALSE for _ in range(num_atoms)])
    return app(app(church(num_atoms), lam(step)), bottom)


# Example 1 (domain {a}): a fact, a chain, a conjunction (AND), and a disjunction (OR).
#   p(a).  q(X):-p(X).  r(X):-p(X),s(X).  t(X):-q(X).  t(X):-r(X).
# atoms: p(a)=0, q(a)=1, r(a)=2, s(a)=3, t(a)=4  (s(a) has no fact, so r(a) is false).
_CONJ_CLAUSES = (
    (0, ()),
    (1, (0,)),
    (2, (0, 3)),
    (4, (1,)),
    (4, (2,)),
)
DATALOG_CONJ_T: Node = build(app(_proj(4, 5), datalog_model(5, _CONJ_CLAUSES)))  # t(a): true
DATALOG_CONJ_R: Node = build(app(_proj(2, 5), datalog_model(5, _CONJ_CLAUSES)))  # r(a): false

# Example 2 (domain {a,b,c,d}): recursive reachability from a along edges a->b->c (d unreachable).
#   reach(a).  reach(b):-reach(a).  reach(c):-reach(b).
# atoms: reach(a)=0, reach(b)=1, reach(c)=2, reach(d)=3.
_REACH_CLAUSES = (
    (0, ()),
    (1, (0,)),
    (2, (1,)),
)
DATALOG_REACH_C: Node = build(app(_proj(2, 4), datalog_model(4, _REACH_CLAUSES)))  # reach(c): true
DATALOG_REACH_D: Node = build(app(_proj(3, 4), datalog_model(4, _REACH_CLAUSES)))  # reach(d): false

# Reachability over a directed graph WITH A CYCLE (a -> b -> c -> a), plus c -> d; e is isolated.
# atoms: reach(a)=0, reach(b)=1, reach(c)=2, reach(d)=3, reach(e)=4.
_GRAPH_CLAUSES = (
    (0, ()),     # reach(a): the source
    (1, (0,)),   # reach(b) :- reach(a)   edge a -> b
    (2, (1,)),   # reach(c) :- reach(b)   edge b -> c
    (0, (2,)),   # reach(a) :- reach(c)   edge c -> a (closes the cycle)
    (3, (2,)),   # reach(d) :- reach(c)   edge c -> d
)
GRAPH_REACH_D: Node = build(app(_proj(3, 5), datalog_model(5, _GRAPH_CLAUSES)))  # reachable: true
GRAPH_REACH_E: Node = build(app(_proj(4, 5), datalog_model(5, _GRAPH_CLAUSES)))  # unreachable: false

# Andersen-style points-to (alias) analysis as monotone Datalog.
# Program: a = new o1; b = a; c = b. Vars a,b,c and objects o1,o2; atom pointsTo(v,o) = 2*v + o.
_POINTSTO_CLAUSES = (
    (0, ()),     # pointsTo(a,o1): a = new o1
    (2, (0,)),   # pointsTo(b,o1) :- pointsTo(a,o1)   (b = a)
    (3, (1,)),   # pointsTo(b,o2) :- pointsTo(a,o2)
    (4, (2,)),   # pointsTo(c,o1) :- pointsTo(b,o1)   (c = b)
    (5, (3,)),   # pointsTo(c,o2) :- pointsTo(b,o2)
)
POINTSTO_C_O1: Node = build(app(_proj(4, 6), datalog_model(6, _POINTSTO_CLAUSES)))  # c -> o1: true
POINTSTO_C_O2: Node = build(app(_proj(5, 6), datalog_model(6, _POINTSTO_CLAUSES)))  # c -> o2: false


# =====================================================================
# Tree DP and game search: built constructor nodes and interning-aware assembly helpers.
# =====================================================================

# Built (interned) Node forms, so a DAG can be assembled bottom-up at the node level: the HOAS
# builders would re-invoke a shared sub-builder once per reference, unfolding the sharing, whereas
# reusing the built Node keeps both the construction and the DP linear in the depth.
TREE_NODE_NODE: Node = build(TREE_NODE)
TREE_LEAF_NODE: Node = build(TREE_LEAF)
TREE_ANY_NODE: Node = build(TREE_ANY)
_FALSE_NODE: Node = build(FALSE)


def tree_node(left: Builder, right: Builder) -> Builder:
    return app(app(TREE_NODE, left), right)


def tree_leaf(value: Builder) -> Builder:
    return app(TREE_LEAF, value)


def tree_any(tree: Builder) -> Builder:
    return app(TREE_ANY, tree)


def shared_false_tree(depth: int) -> Node:
    """A perfect binary tree of the given depth with every leaf FALSE, assembled bottom-up so the
    two children of each node are the same object. The result is a DAG of ``depth + 1`` distinct
    interned nodes that unfolds to ``2 ** depth`` leaves, built in time linear in ``depth``.
    """
    if depth < 0:
        raise ValueError("depth must be nonnegative")
    node = make_app(TREE_LEAF_NODE, _FALSE_NODE)  # leaf FALSE
    for _ in range(depth):
        node = make_app(make_app(TREE_NODE_NODE, node), node)
    return node


def any_false_dp(depth: int) -> Node:
    """The tree DP ``tree_any`` over ``shared_false_tree(depth)``: each distinct subtree is one
    interned node, so the DP computes it once, returning FALSE in time linear in ``depth``."""
    return make_app(TREE_ANY_NODE, shared_false_tree(depth))


MAX_NODE_NODE: Node = build(MAX_NODE)
MIN_NODE_NODE: Node = build(MIN_NODE)
GAME_LEAF_NODE: Node = build(GAME_LEAF)
MINIMAX_NODE: Node = build(MINIMAX)
_TRUE_NODE: Node = build(TRUE)


def game_max(left: Node, right: Node) -> Node:
    return make_app(make_app(MAX_NODE_NODE, left), right)


def game_min(left: Node, right: Node) -> Node:
    return make_app(make_app(MIN_NODE_NODE, left), right)


def game_leaf(value: Node) -> Node:
    return make_app(GAME_LEAF_NODE, value)


def minimax(position: Node) -> Node:
    return make_app(MINIMAX_NODE, position)


# =====================================================================
# Imperative stream demo: GEN's cyclic output decoded to a Python generator.
# =====================================================================

_STREAM_BASE = 6_000_000


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
