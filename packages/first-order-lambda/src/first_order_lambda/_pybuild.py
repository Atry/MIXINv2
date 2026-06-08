"""Lambda-term builders for the generic ``_pyast`` Scott encoding of a Python AST.

The compiler's target is a real Python ``ast`` Scott-encoded by ``_pyast`` (reflection-derived from the
``ast`` node classes). To let the ``COMPILE`` lambda term EMIT that generic encoding directly, this
module gives lambda-term "smart constructors", one per ``ast`` node the compiler produces, that fill in
the boilerplate fields the generic ``_pyast.decode`` reads (``decorator_list=[]``, ``returns=None``,
``ctx=Load()``, ...). Each is a thin wrapper over ``_pyast``'s own ``_ctor`` (the n-ary Scott
constructor), ``_kind`` (the field kind-tag pair), and ``_scott_list``, so the values these build are
exactly what ``_pyast.decode`` expects: ``_pyast.decode(build(<smart ctor>)) == <the ast node>``.

A node is ``_ctor(tag, fields)`` where ``tag`` is the class's index in ``_pyast.SUPPORTED`` and each
field is ``_kind(kind, payload)``; a list field's payload is a Scott list whose elements are themselves
kind-tagged fields (so a list of nodes is a Scott list of ``_field_node`` values).
"""

from __future__ import annotations

import ast

from first_order_lambda._dsl import Builder
from first_order_lambda._prelude import SCOTT_NIL, church
from first_order_lambda._pyast import (
    _K_BOOL,
    _K_IDENT,
    _K_INT,
    _K_LIST,
    _K_NODE,
    _K_NONE,
    _K_STR,
    _TAG,
    _ctor,
    _kind,
    _scott_list,
)

# --- field constructors (a field is a <kind, payload> pair the decoder dispatches on) -----------


def _node(cls: "type[ast.AST]", fields: "list[Builder]") -> Builder:
    """The Scott value for an ``ast`` node of class ``cls`` with the given (kind-tagged) fields."""
    return _ctor(_TAG[cls], fields)


def field_node(child: Builder) -> Builder:
    return _kind(_K_NODE, child)


def field_list(elements: Builder) -> Builder:
    """A list field; ``elements`` is a Scott list whose items are themselves kind-tagged fields."""
    return _kind(_K_LIST, elements)


def field_int(nat: Builder) -> Builder:
    return _kind(_K_INT, nat)


def field_str(char_codes: Builder) -> Builder:
    """A string field; ``char_codes`` is a Scott list of Nat character codes."""
    return _kind(_K_STR, char_codes)


def field_ident(path: Builder) -> Builder:
    """An identifier field; ``path`` is a Scott list of Nats (an AST path). The single ``_pyast``
    decoder renders it ``v_<int>_<int>...`` for every runtime, so the lambda compiler emits only the
    path, never a rendered string."""
    return _kind(_K_IDENT, path)


def field_bool(nat: Builder) -> Builder:
    return _kind(_K_BOOL, nat)


def field_none() -> Builder:
    return _kind(_K_NONE, church(0))


def char_codes(text: str) -> Builder:
    """The Scott list of character codes for a fixed Python string (a baked-in literal)."""
    return _scott_list([church(ord(character)) for character in text])


def field_node_list(node_fields: Builder) -> Builder:
    """Convenience: a list field over a Scott list whose elements are already ``field_node`` values."""
    return field_list(node_fields)


# --- smart constructors, one per ast node the compiler emits -------------------------------------
# A list-valued argument is a Scott list of ALREADY kind-tagged fields (``field_node`` of each node, or
# ``field_str`` of each name), matching what the decoder's ``_K_LIST`` case feeds back to ``_decode_field``.


def py_load() -> Builder:
    return _node(ast.Load, [])


def py_store() -> Builder:
    return _node(ast.Store, [])


def py_is() -> Builder:
    return _node(ast.Is, [])


def py_name(name_field: Builder, ctx: Builder) -> Builder:
    """``ast.Name(id=<name>, ctx=<ctx>)``; ``name_field`` an already-kind-tagged name field
    (``field_str`` for a fixed name, ``field_ident`` for a variable's AST path)."""
    return _node(ast.Name, [name_field, field_node(ctx)])


def py_arg(name_field: Builder) -> Builder:
    """``ast.arg(arg=<name>, annotation=None, type_comment=None)``; ``name_field`` a name field."""
    return _node(ast.arg, [name_field, field_none(), field_none()])


def py_arguments(arg_fields: Builder) -> Builder:
    """``ast.arguments`` with only positional ``args`` populated; ``arg_fields`` a Scott list of
    ``field_node(arg)``. Order: posonlyargs, args, vararg, kwonlyargs, kw_defaults, kwarg, defaults."""
    return _node(
        ast.arguments,
        [
            field_list(SCOTT_NIL),
            field_list(arg_fields),
            field_none(),
            field_list(SCOTT_NIL),
            field_list(SCOTT_NIL),
            field_none(),
            field_list(SCOTT_NIL),
        ],
    )


def py_lambda(arg_field: Builder, body: Builder) -> Builder:
    """``lambda <arg>: <body>`` with a single positional parameter; ``arg_field`` a name field."""
    args = py_arguments(_scott_list([field_node(py_arg(arg_field))]))
    return _node(ast.Lambda, [field_node(args), field_node(body)])


def py_lambda0(body: Builder) -> Builder:
    """``lambda: <body>`` with no parameters (for a call-by-name ``Thunk(lambda: e)``)."""
    return _node(ast.Lambda, [field_node(py_arguments(SCOTT_NIL)), field_node(body)])


def py_call(func: Builder, arg_fields: Builder) -> Builder:
    """``<func>(<args...>)``; ``arg_fields`` a Scott list of ``field_node(arg)``; no keywords."""
    return _node(ast.Call, [field_node(func), field_list(arg_fields), field_list(SCOTT_NIL)])


def py_function_def(name_field: Builder, args_node: Builder, body_fields: Builder) -> Builder:
    """``def <name>(<args>): <body>`` with no decorators/returns/type comment; ``body_fields`` a Scott
    list of ``field_node(stmt)``.

    The fields are keyed by name and ordered by the RUNNING ``ast.FunctionDef._fields``, so the emitted
    node matches the host Python version: Python 3.12+ added ``type_params`` (an empty list here), which
    the generic decoder reflects, so the call-by-need target round-trips on 3.11 and on 3.12+ alike.
    """
    by_name = {
        "name": name_field,
        "args": field_node(args_node),
        "body": field_list(body_fields),
        "decorator_list": field_list(SCOTT_NIL),
        "returns": field_none(),
        "type_comment": field_none(),
        "type_params": field_list(SCOTT_NIL),
    }
    return _node(ast.FunctionDef, [by_name[name] for name in ast.FunctionDef._fields])


def py_assign(target: Builder, value: Builder) -> Builder:
    """``<target> = <value>`` with a single target. Order: targets, value, type_comment."""
    return _node(ast.Assign, [field_list(_scott_list([field_node(target)])), field_node(value), field_none()])


def py_nonlocal(name_fields: Builder) -> Builder:
    """``nonlocal <names...>``; ``name_fields`` a Scott list of ``field_str(codes)``."""
    return _node(ast.Nonlocal, [field_list(name_fields)])


def py_if(test: Builder, body_fields: Builder) -> Builder:
    """``if <test>: <body>`` with no else; ``body_fields`` a Scott list of ``field_node(stmt)``."""
    return _node(ast.If, [field_node(test), field_list(body_fields), field_list(SCOTT_NIL)])


def py_return(value: Builder) -> Builder:
    return _node(ast.Return, [field_node(value)])


def py_compare_is(left: Builder, right: Builder) -> Builder:
    """``<left> is <right>``. Order: left, ops, comparators."""
    return _node(
        ast.Compare,
        [
            field_node(left),
            field_list(_scott_list([field_node(py_is())])),
            field_list(_scott_list([field_node(right)])),
        ],
    )


def py_module(stmt_fields: Builder) -> Builder:
    """``ast.Module``; ``stmt_fields`` a Scott list of ``field_node(stmt)``. Order: body, type_ignores."""
    return _node(ast.Module, [field_list(stmt_fields), field_list(SCOTT_NIL)])


def py_constant_int(nat: Builder) -> Builder:
    """``ast.Constant(value=<int>, kind=None)`` with an integer (Nat) value."""
    return _node(ast.Constant, [field_int(nat), field_none()])
