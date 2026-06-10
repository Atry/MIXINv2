"""Lexical analysis: a deterministic finite automaton run over an input, in the pure calculus.

Regular languages are the archetypal rational behaviour. A DFA is a finite (cyclic) transition
graph; running it is a fold over the input that threads the current state. Here states and symbols
are two-way Scott selectors (reusing TRUE/FALSE), the automaton recognises strings with an even
number of ``a``s over the alphabet {a, b}, and acceptance is read as a Church boolean. The automaton
is encoded with no construct added to the calculus.
"""

from __future__ import annotations

from co_lambda._dsl import app, build, lam
from co_lambda._prelude import FALSE, SCOTT_NIL, TRUE, Y, cons
from co_lambda._render import render

_TRUE = render(build(TRUE))
_FALSE = render(build(FALSE))

# States: even = TRUE, odd = FALSE. Symbols: a = TRUE, b = FALSE. Both are two-way selectors.
# delta state sym = state (sym odd even) (sym even odd):
#   from even, an a goes to odd and a b stays even; from odd, an a goes to even and a b stays odd.
_DELTA = lam(lambda state: lam(lambda symbol: app(
    app(state, app(app(symbol, FALSE), TRUE)),
    app(app(symbol, TRUE), FALSE),
)))

# run = Y (lambda self. lambda state. lambda input. input (lambda h. lambda t. self (delta state h) t)
#                                                          state)
_RUN = app(
    Y,
    lam(lambda self_recursion: lam(lambda state: lam(lambda input_list: app(
        app(
            input_list,
            lam(lambda head: lam(lambda tail: app(
                app(self_recursion, app(app(_DELTA, state), head)), tail))),
        ),
        state,  # at nil, return the current state
    )))),
)

# accept iff the final state is even (= TRUE).
_ACCEPTS = lam(lambda state: app(app(state, TRUE), FALSE))


def _accepts(symbols) -> str:
    word = SCOTT_NIL
    for symbol in reversed(symbols):
        word = cons(symbol, word)
    return render(build(app(_ACCEPTS, app(app(_RUN, TRUE), word))))


def test_dfa_accepts_even_number_of_a() -> None:
    assert _accepts([]) == _TRUE                       # zero a's
    assert _accepts([TRUE, TRUE]) == _TRUE             # "aa"
    assert _accepts([TRUE, FALSE, FALSE, TRUE]) == _TRUE  # "abba"


def test_dfa_rejects_odd_number_of_a() -> None:
    assert _accepts([TRUE]) == _FALSE                  # "a"
    assert _accepts([TRUE, FALSE]) == _FALSE           # "ab"
    assert _accepts([TRUE, TRUE, TRUE]) == _FALSE      # "aaa"
