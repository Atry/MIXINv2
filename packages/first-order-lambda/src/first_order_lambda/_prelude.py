"""Scott encodings and example terms, written with the HOAS DSL (test data, not re-exports).

The combinators are HOAS ``Builder``s (compose with ``app``); the example terms are built
``Node``s ready to interpret.
"""

from __future__ import annotations

from first_order_lambda._ast import Node
from first_order_lambda._dsl import Builder, app, build, lam

# Combinators (HOAS builders).
IDENTITY: Builder = lam(lambda x: x)
SCOTT_CONS: Builder = lam(
    lambda h: lam(lambda t: lam(lambda c: lam(lambda n: app(app(c, h), t))))
)
SCOTT_NIL: Builder = lam(lambda c: lam(lambda n: n))
SCOTT_PRESENT: Builder = lam(lambda a: lam(lambda b: a))  # the first Scott constructor
SCOTT_EMPTY: Builder = lam(lambda a: lam(lambda b: b))  # the second Scott constructor
ZERO: Builder = lam(lambda s: lam(lambda z: z))  # a closed element marker
KESTREL: Builder = lam(lambda x: lam(lambda y: x))  # K = lambda x. lambda y. x
SELF_APPLY: Builder = lam(lambda x: app(x, x))
Y: Builder = lam(
    lambda f: app(
        lam(lambda x: app(f, app(x, x))),
        lam(lambda x: app(f, app(x, x))),
    )
)


def cons(head: Builder, tail: Builder) -> Builder:
    return app(app(SCOTT_CONS, head), tail)


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
