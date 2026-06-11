"""Pure-lambda prelude: the combinators and Scott data vocabulary, written as literal HOAS.

This module is pure lambda calculus (one of the four strictly separated kinds: codec / sugar /
runtime / pure-lambda source): every top-level binding is a ``Builder`` lambda term, transcribed
one-to-one through the ``_dsl`` notation. Encodings of Python data (Church numeral rendering,
Scott-list building) live in ``_codec``; appliers and other writing sugar live in ``_sugar``; the
built example ``Node``s and the demo encoders (Datalog, tree DP, game search harnesses) live in
``_examples``.
"""

from __future__ import annotations

from co_lambda._dsl import Builder, app, lam

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
AND: Builder = lam(lambda p: lam(lambda q: app(app(p, q), FALSE)))  # p and q
OR: Builder = lam(lambda p: lam(lambda q: app(app(p, TRUE), q)))    # p or q

# Church-numeral literals the prelude's own terms need (the general renderer is ``_codec.church``).
ZERO: Builder = lam(lambda s: lam(lambda z: z))
ONE: Builder = lam(lambda s: lam(lambda z: app(s, z)))

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

# factorial n = if n = 0 then 1 else n * factorial (n - 1); the Church boolean selects.
FACTORIAL: Builder = app(
    Y,
    lam(lambda f: lam(lambda n: app(
        app(app(IS_ZERO, n), ONE),
        app(app(MULT, n), app(f, app(PRED, n))),
    ))),
)

# fib n = if n = 0 then 0 else if (n - 1) = 0 then 1 else fib (n-1) + fib (n-2)
FIBONACCI: Builder = app(
    Y,
    lam(lambda f: lam(lambda n: app(
        app(app(IS_ZERO, n), ZERO),
        app(
            app(app(IS_ZERO, app(PRED, n)), ONE),
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
                lam(lambda head: lam(lambda tail: app(
                    app(SCOTT_CONS, app(f, head)),
                    app(self_recursion, tail),
                ))),
            ),
            SCOTT_NIL,
        ))),
    )
)

# =====================================================================
# Dynamic programming with a tree state space: memoisation for free.
#
# A binary tree is Scott-encoded with two constructors, node(l, r) and leaf(v); a tree DP is an
# ordinary Y-recursion whose subproblems are the subtrees. Interning makes structurally-identical
# subtrees one node, so a DP over a DAG-compressed tree computes each distinct subtree once.
# =====================================================================

TREE_NODE: Builder = lam(
    lambda l: lam(lambda r: lam(lambda on_node: lam(lambda on_leaf: app(app(on_node, l), r))))
)
TREE_LEAF: Builder = lam(lambda v: lam(lambda on_node: lam(lambda on_leaf: app(on_leaf, v))))

# tree_any t = OR over the leaves of t of the leaf's boolean. As a tree DP:
#   tree_any = Y (lambda self. lambda t. t (lambda l. lambda r. OR (self l) (self r)) (lambda v. v))
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

# =====================================================================
# Minimax / AND-OR game search with a transposition table for free.
#
# A game position is a MAX node (OR over moves), a MIN node (AND over moves), or a terminal LEAF
# carrying a Boolean outcome. A transposition is the same interned node, so its value is computed
# once: interning is the transposition table.
# =====================================================================

MAX_NODE: Builder = lam(lambda l: lam(lambda r: lam(
    lambda on_max: lam(lambda on_min: lam(lambda on_leaf: app(app(on_max, l), r))))))
MIN_NODE: Builder = lam(lambda l: lam(lambda r: lam(
    lambda on_max: lam(lambda on_min: lam(lambda on_leaf: app(app(on_min, l), r))))))
GAME_LEAF: Builder = lam(lambda v: lam(
    lambda on_max: lam(lambda on_min: lam(lambda on_leaf: app(on_leaf, v)))))

# minimax = Y (lambda self. lambda pos. pos (max: OR (self l) (self r)) (min: AND (self l) (self r))
#                                            (leaf: lambda v. v))
MINIMAX: Builder = app(
    Y,
    lam(lambda self_recursion: lam(lambda position: app(app(app(
        position,
        lam(lambda left: lam(lambda right: app(
            app(OR, app(self_recursion, left)), app(self_recursion, right)))),       # MAX: OR
        ),
        lam(lambda left: lam(lambda right: app(
            app(AND, app(self_recursion, left)), app(self_recursion, right)))),       # MIN: AND
        ),
        lam(lambda value: value),                                                     # LEAF
    ))),
)
