"""Encodings and example terms, written with the HOAS DSL (test data, not re-exports).

The combinators are HOAS ``Builder``s (compose with ``app``); the example terms are built
``Node``s ready to interpret. Includes pure-lambda combinators, Scott-encoded lists for cyclic
data with the ordinary singly-linked-list ``map`` (which folds a cyclic list into a finite
circular list), and Church numerals with Peano arithmetic (succ, plus, mult, exp, predecessor,
is-zero), factorial and Fibonacci via ``Y``.
"""

from __future__ import annotations

from first_order_lambda._ast import Node
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
