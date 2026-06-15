"""``node_case``: the one runtime node-observation primitive for host-compiled local analyses.

It is a call-by-need value (the CODEGEN_NEED protocol: a value is a 0-arg thunk forced by ``()``; a
forced function takes one thunk argument and returns a value), curried over the node and the three
handlers, dispatching on the node's LITERAL ``Var`` / ``Lam`` / ``App`` constructor with no reduction:
``on_var`` receives the de Bruijn index as a Church numeral, ``on_lam`` the body node, ``on_app`` the
function then argument nodes -- each child a thunk yielding the child node, so an analysis recurses.
"""

from __future__ import annotations

from co_lambda._ast import make_app, make_lam, make_var
from co_lambda._runtime import node_case


def _drive(node):
    """Drive ``node_case`` over ``node`` call-by-need; the handlers tag the branch and return children."""
    on_var = lambda: (lambda index_thunk: (lambda: ("var", index_thunk)))
    on_lam = lambda: (lambda body_thunk: (lambda: ("lam", body_thunk)))
    on_app = lambda: (lambda function_thunk: (lambda: (lambda argument_thunk: (
        lambda: ("app", function_thunk, argument_thunk)))))
    forced = node_case()(lambda: node)()(on_var)()(on_lam)()(on_app)
    return forced()


def _church_to_int(forced_church) -> int:
    """A forced call-by-need Church numeral (``take_f``) to a Python int via an int successor."""
    successor = lambda x_thunk: (lambda: x_thunk() + 1)
    return forced_church(lambda: successor)()(lambda: 0)()


def test_node_case_dispatches_var_to_the_index() -> None:
    tag, index_thunk = _drive(make_var(3))
    assert tag == "var"
    assert _church_to_int(index_thunk()) == 3


def test_node_case_dispatches_lam_to_the_body() -> None:
    tag, body_thunk = _drive(make_lam(make_var(0)))
    assert tag == "lam"
    assert body_thunk() == make_var(0)


def test_node_case_dispatches_app_to_the_children() -> None:
    tag, function_thunk, argument_thunk = _drive(make_app(make_var(5), make_var(7)))
    assert tag == "app"
    assert function_thunk() == make_var(5)
    assert argument_thunk() == make_var(7)
