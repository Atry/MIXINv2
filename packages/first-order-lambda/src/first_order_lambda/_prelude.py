"""Encodings and example terms, written with the HOAS DSL (test data, not re-exports).

The combinators are HOAS ``Builder``s (compose with ``app``); the example terms are built
``Node``s ready to interpret. Includes pure-lambda combinators, Scott-encoded lists for cyclic
data with the ordinary singly-linked-list ``map`` (which folds a cyclic list into a finite
circular list), and Church numerals with Peano arithmetic (succ, plus, mult, exp, predecessor,
is-zero), factorial and Fibonacci via ``Y``.
"""

from __future__ import annotations

from first_order_lambda._ast import Node, make_app
from first_order_lambda._dsl import Builder, app, build, lam

# Combinators.
IDENTITY: Builder = lam(lambda x: x)
KESTREL: Builder = lam(lambda x: lam(lambda y: x))  # K = lambda x. lambda y. x
SELF_APPLY: Builder = lam(lambda x: app(x, x))
Y: Builder = lam(
    lambda f: app(
        lam(lambda x: app(f, app(x, x))),
        lam(lambda x: app(f, app(x, x))),
    )
)

# Church booleans.
TRUE: Builder = lam(lambda a: lam(lambda b: a))
FALSE: Builder = lam(lambda a: lam(lambda b: b))


def church(n: int) -> Builder:
    """The Church numeral ``n`` = ``lambda s. lambda z. s (s ... (s z))`` (``n`` applications)."""
    if n < 0:
        raise ValueError("Church numerals are nonnegative")

    def body(s: Builder, z: Builder) -> Builder:
        acc = z
        for _ in range(n):
            acc = app(s, acc)
        return acc

    return lam(lambda s: lam(lambda z: body(s, z)))


# Peano arithmetic on Church numerals.
SUCC: Builder = lam(lambda n: lam(lambda s: lam(lambda z: app(s, app(app(n, s), z)))))
PLUS: Builder = lam(
    lambda m: lam(lambda n: lam(lambda s: lam(lambda z: app(app(m, s), app(app(n, s), z)))))
)
MULT: Builder = lam(lambda m: lam(lambda n: lam(lambda s: app(m, app(n, s)))))
EXP: Builder = lam(lambda m: lam(lambda n: app(n, m)))  # m ^ n = n m
IS_ZERO: Builder = lam(lambda n: app(app(n, lam(lambda x: FALSE)), TRUE))
PRED: Builder = lam(
    lambda n: lam(lambda s: lam(lambda z: app(
        app(
            app(n, lam(lambda g: lam(lambda h: app(h, app(g, s))))),
            lam(lambda u: z),
        ),
        lam(lambda u: u),
    )))
)


def _if(condition: Builder, then: Builder, otherwise: Builder) -> Builder:
    # A Church boolean selects: (b then otherwise).
    return app(app(condition, then), otherwise)


# factorial n = if n = 0 then 1 else n * factorial (n - 1)
FACTORIAL: Builder = app(
    Y,
    lam(lambda f: lam(lambda n: _if(
        app(IS_ZERO, n),
        church(1),
        app(app(MULT, n), app(f, app(PRED, n))),
    ))),
)

# fib n = if n = 0 then 0 else if (n - 1) = 0 then 1 else fib (n-1) + fib (n-2)
FIBONACCI: Builder = app(
    Y,
    lam(lambda f: lam(lambda n: _if(
        app(IS_ZERO, n),
        church(0),
        _if(
            app(IS_ZERO, app(PRED, n)),
            church(1),
            app(
                app(PLUS, app(f, app(PRED, n))),
                app(f, app(PRED, app(PRED, n))),
            ),
        ),
    ))),
)

# Scott-encoded lists, for cyclic data.
SCOTT_CONS: Builder = lam(
    lambda h: lam(lambda t: lam(lambda c: lam(lambda n: app(app(c, h), t))))
)
SCOTT_NIL: Builder = lam(lambda c: lam(lambda n: n))
SCOTT_PRESENT: Builder = lam(lambda a: lam(lambda b: a))  # = TRUE / first Scott constructor
ZERO: Builder = lam(lambda s: lam(lambda z: z))  # = church 0, a closed element marker


def cons(head: Builder, tail: Builder) -> Builder:
    return app(app(SCOTT_CONS, head), tail)


# The ordinary singly-linked-list map: nothing is cycle-aware. map f = Y (lambda self.
# lambda lst. lst (lambda h. lambda t. cons (f h) (self t)) nil). The recursion is guarded
# (a cons is exposed before the recursive call), so on a cyclic list the recursive
# application self t re-enters the same closed position and the least fixpoint folds it into
# a finite cyclic result, where head reduction would unfold the mapped stream forever.
MAP: Builder = lam(
    lambda f: app(
        Y,
        lam(lambda self_recursion: lam(lambda source: app(
            app(
                source,
                lam(lambda head: lam(lambda tail: cons(
                    app(f, head),
                    app(self_recursion, tail),
                ))),
            ),
            SCOTT_NIL,
        ))),
    )
)


def map_list(function: Builder, source: Builder) -> Builder:
    return app(app(MAP, function), source)


# Example terms (built de Bruijn nodes). The calculus is pure: cyclic and recursive data
# are written with Y, and interning folds the structurally-repeating positions.
IDENTITY_TERM: Node = build(IDENTITY)
KESTREL_TERM: Node = build(KESTREL)
OMEGA: Node = build(app(SELF_APPLY, SELF_APPLY))  # an unproductive cycle
FINITE_LIST: Node = build(cons(ZERO, SCOTT_NIL))  # cons 0 nil

# r = cons 0 r : the cyclic stream, written Y (cons 0) (no recursion binder needed).
CYCLIC_ZEROS: Node = build(app(Y, app(SCOTT_CONS, ZERO)))

# letrec x = x : an unproductive head cycle, written Y (lambda x. x).
LOOP: Node = build(app(Y, IDENTITY))


# =====================================================================
# Pure Datalog as a monotone Church-boolean least fixpoint.
#
# A ground Datalog program (no function symbols, so a finite Herbrand base) is a monotone
# Boolean equation system over its ground atoms. A model is a Church tuple of booleans; the
# immediate-consequence operator T_P is a tuple-to-tuple function (each atom's new truth is an
# OR over its clauses of an AND over the clause body); the least Herbrand model is T_P iterated
# |HB| times from the all-false tuple -- a bounded, total term (no Y). A goal atom is a
# projection, which renders to TRUE or FALSE.
# =====================================================================

AND: Builder = lam(lambda p: lam(lambda q: app(app(p, q), FALSE)))  # p and q
OR: Builder = lam(lambda p: lam(lambda q: app(app(p, TRUE), q)))    # p or q


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
# The least fixpoint handles the cycle and terminates: reach(d) is true (reached through the
# cycle), reach(e) is false. This is graph reachability / transitive closure, and the same shape
# as model-checking reachability of a bad state in a finite transition system.
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

# Andersen-style points-to (alias) analysis as monotone Datalog, the basis of alias analysis in
# compilers:  pointsTo(p,o) :- new(p,o);  pointsTo(p,o) :- assign(p,q), pointsTo(q,o).
# Program: a = new o1; b = a; c = b. Vars a,b,c and objects o1,o2; atom pointsTo(v,o) = 2*v + o.
# So c points to o1 (through the copy chain) but not o2 (o2 is never allocated).
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
# Dynamic programming with a tree state space: memoisation for free.
#
# A binary tree is Scott-encoded with two constructors, node(l, r) and leaf(v); a tree DP is an
# ordinary Y-recursion whose subproblems are the subtrees. Interning makes structurally-identical
# subtrees one node, so a DP over a DAG-compressed tree (both children of every node shared)
# computes each distinct subtree once: the exponential recomputation of the naive tree recursion
# collapses to a linear pass. This is the memoisation a pure lambda-calculus lacks without a
# decidable identity on subproblems (value equality of closures is undecidable).
# =====================================================================

TREE_NODE: Builder = lam(
    lambda l: lam(lambda r: lam(lambda on_node: lam(lambda on_leaf: app(app(on_node, l), r))))
)
TREE_LEAF: Builder = lam(lambda v: lam(lambda on_node: lam(lambda on_leaf: app(on_leaf, v))))


def tree_node(left: Builder, right: Builder) -> Builder:
    return app(app(TREE_NODE, left), right)


def tree_leaf(value: Builder) -> Builder:
    return app(TREE_LEAF, value)


# tree_any t = OR over the leaves of t of the leaf's boolean. As a tree DP:
#   tree_any = Y (lambda self. lambda t. t (lambda l. lambda r. OR (self l) (self r)) (lambda v. v))
# The recursive calls self l and self r are the subtree subproblems.
TREE_ANY: Builder = app(
    Y,
    lam(lambda self_recursion: lam(lambda tree: app(
        app(
            tree,
            lam(lambda left: lam(lambda right: app(
                app(OR, app(self_recursion, left)), app(self_recursion, right)
            ))),
        ),
        lam(lambda value: value),
    ))),
)


def tree_any(tree: Builder) -> Builder:
    return app(TREE_ANY, tree)


# Built (interned) Node forms, so the DAG below can be assembled bottom-up at the node level: the
# HOAS builders would re-invoke a shared sub-builder once per reference, unfolding the sharing and
# costing O(2 ** depth) just to construct the term, whereas reusing the built Node keeps both the
# construction and the DP linear in the depth.
TREE_NODE_NODE: Node = build(TREE_NODE)
TREE_LEAF_NODE: Node = build(TREE_LEAF)
TREE_ANY_NODE: Node = build(TREE_ANY)
_FALSE_NODE: Node = build(FALSE)


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
    """The tree DP ``tree_any`` over ``shared_false_tree(depth)``: its state space is the DAG, and
    because identical subtrees are one interned node the DP computes each distinct subtree once,
    returning FALSE in time linear in ``depth`` where the naive tree recursion is ``2 ** depth``.
    """
    return make_app(TREE_ANY_NODE, shared_false_tree(depth))
