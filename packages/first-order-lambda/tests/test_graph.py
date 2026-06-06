"""Graph reachability over a directed graph with a cycle, as a Datalog least fixpoint.

The graph a -> b -> c -> a (a cycle) plus c -> d is read by the same bounded boolean fixpoint as
Datalog: the least fixpoint handles the cycle and terminates. reach(d) is true (reached through the
cycle), reach(e) is false (e is isolated). This is graph reachability / transitive closure, and the
shape of model-checking reachability of a bad state in a finite transition system.
"""

from __future__ import annotations

from first_order_lambda._dsl import build
from first_order_lambda._prelude import FALSE, GRAPH_REACH_D, GRAPH_REACH_E, TRUE
from first_order_lambda._render import render

_TRUE = render(build(TRUE))
_FALSE = render(build(FALSE))


def test_reachable_through_cycle() -> None:
    assert render(GRAPH_REACH_D) == _TRUE


def test_isolated_node_is_unreachable() -> None:
    assert render(GRAPH_REACH_E) == _FALSE
