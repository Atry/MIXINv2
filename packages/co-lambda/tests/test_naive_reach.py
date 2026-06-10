"""A naive external query (an ordinary Y-recursive lambda-term) terminates under interning.

No property need be baked into the constructors: the recursive application nodes the query
builds intern structurally, so tabling folds them. Naive head reduction would loop forever on
the cyclic stream; the interpreter folds it.
"""

from co_lambda._dsl import app, build, lam
from co_lambda._prelude import SCOTT_CONS, SCOTT_PRESENT, Y, ZERO
from co_lambda._render import render

# walk = Y (lambda self. lambda lst. lst (lambda h. lambda t. self t) present)
# An ordinary recursive walk down a Scott stream; nothing is baked into cons/nil.
WALK = app(
    Y,
    lam(lambda s: lam(lambda lst: app(
        app(lst, lam(lambda h: lam(lambda t: app(s, t)))),
        SCOTT_PRESENT,
    ))),
)
WALK_CYCLIC = build(app(WALK, app(Y, app(SCOTT_CONS, ZERO))))  # walk (Y (cons 0))


def test_naive_query_over_cyclic_terminates() -> None:
    # The walk searches for nil and never finds it; tabling folds the cycle to the bottom leaf
    # instead of diverging, so the naive external query terminates.
    assert render(WALK_CYCLIC) == "⊥"
