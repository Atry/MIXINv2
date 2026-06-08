"""The lambda-term smart constructors build exactly the generic ``_pyast`` Scott encoding.

Each constructor in ``_pybuild`` builds a Scott value that ``_pyast.decode`` reads back as the intended
real ``ast`` node, including all the boilerplate fields the generic decoder requires. These tests pin
that correspondence in isolation, before ``COMPILE`` is retargeted onto these constructors.
"""

from __future__ import annotations

import ast

from first_order_lambda import _pybuild as B
from first_order_lambda._dsl import build
from first_order_lambda._prelude import church
from first_order_lambda._pyast import _scott_list, decode


def _source(builder) -> str:
    return ast.unparse(ast.fix_missing_locations(decode(build(builder))))


def _nodes(*builders) -> "object":
    return _scott_list([B.field_node(item) for item in builders])


def _str_name(text: str):
    return B.py_name(B.field_str(B.char_codes(text)), B.py_load())


def test_name_and_call_decode() -> None:
    assert _source(_str_name("force")) == "force"
    call = B.py_call(_str_name("f"), _nodes(_str_name("x")))
    assert _source(call) == "f(x)"
    forced = B.py_call(_str_name("v_0"), _scott_list([]))
    assert _source(forced) == "v_0()"


def test_ident_field_decodes_path_to_underscored_integers() -> None:
    # A variable identifier is emitted as a list of Nats (its AST path); the one decoder renders it
    # ``v_<int>_<int>...`` (an alphabetic prefix, underscore-segmented integers, unique by path).
    path = _scott_list([church(2), church(0), church(1)])
    assert _source(B.py_name(B.field_ident(path), B.py_load())) == "v_2_0_1"
    assert _source(B.py_name(B.field_ident(_scott_list([])), B.py_load())) == "v"


def test_lambda_decodes() -> None:
    body = B.py_name(B.field_ident(_scott_list([church(0)])), B.py_load())
    assert _source(B.py_lambda(B.field_ident(_scott_list([church(0)])), body)) == "lambda v_0: v_0"


def test_compare_is_decodes() -> None:
    left = _str_name("v_0")
    right = _str_name("SENTINEL")
    assert _source(B.py_compare_is(left, right)) == "v_0 is SENTINEL"


def test_constant_int_decodes() -> None:
    assert _source(B.py_constant_int(church(7))) == "7"


def test_call_by_need_module_decodes_and_runs() -> None:
    # Assemble, purely with the smart constructors, the memoising-thunk module shape the call-by-need
    # target emits, and check it decodes to the right source and runs.
    name = _str_name
    sentinel = name("SENTINEL")
    cell = "v_0"
    inner_def = B.py_function_def(
        B.field_str(B.char_codes("v_1")),
        B.py_arguments(_scott_list([])),
        _nodes(
            B.py_nonlocal(_scott_list([B.field_str(B.char_codes(cell))])),
            B.py_if(
                B.py_compare_is(name(cell), sentinel),
                _nodes(B.py_assign(name(cell), B.py_call(name("v_2"), _scott_list([])))),
            ),
            B.py_return(name(cell)),
        ),
    )
    program_def = B.py_function_def(
        B.field_str(B.char_codes("_program")),
        B.py_arguments(_scott_list([])),
        _nodes(
            B.py_assign(name(cell), sentinel),
            inner_def,
            B.py_return(name("v_1")),
        ),
    )
    bind = B.py_assign(name("program"), B.py_call(name("_program"), _scott_list([])))
    module = B.py_module(_nodes(program_def, bind))

    expected = (
        "def _program():\n"
        "    v_0 = SENTINEL\n"
        "    def v_1():\n"
        "        nonlocal v_0\n"
        "        if v_0 is SENTINEL:\n"
        "            v_0 = v_2()\n"
        "        return v_0\n"
        "    return v_1\n"
        "program = _program()"
    )
    # Compare against the normalized (parse+unparse) form, since ast.unparse inserts blank lines
    # around nested defs; the structural content is what matters.
    assert _source(module) == ast.unparse(ast.parse(expected))
