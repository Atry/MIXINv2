"""A lambda-calculus to Python compiler written in the lambda-calculus.

The source is a quoted lambda term, a Scott value over ``QVar i`` / ``QLam body`` / ``QApp f a`` (de
Bruijn). ``COMPILE`` is a pure lambda term that, GIVEN a compilation option, maps the quoted source to
a quoted Python expression, a Scott value over ``PyVar level`` / ``PyLam level body`` / ``PyApp f a``
/ ``PyForce e`` / ``PyThunk e``. The option decides the target, in the lambda term itself: under the
call-by-value option an application is a strict call and a variable is a bare name; under the
call-by-name option a variable is forced and an argument is thunked (``force``/``Thunk``), matching
the interpreter's weak-head reduction. So the target-specific codegen lives in the lambda term; Python
only quotes the input, supplies the option, runs the interpreter, and decodes the resulting Scott
Python expression with a single generic decoder.

The interpret target is not a compiled target. It means interpret: re-submit the term to the
interpreter, whose interning gives the genuine cross-graph tabling fold. (The old compiled fixpoint
thunk, a ``fixpoint_cached_property`` per thunk, had no cross-graph tabling and is removed.)
"""

from __future__ import annotations

import ast
from enum import Enum, auto

from first_order_lambda._ast import App, Lam, Node, Var, make_app, make_lam, make_var
from first_order_lambda._dsl import Builder, app, build, lam
from first_order_lambda._prelude import FALSE, PRED, SCOTT_NIL, SUCC, TRUE, church, cons
from first_order_lambda._pyast import _church_to_int, _decode_scott_list, _extract

_PY_BASE = 5_000_000

# The strict (call-by-value) fixpoint combinator Z = lambda f. (lambda x. f (lambda v. x x v)) (...).
# Unlike Y it is eta-expanded under the recursive call, so the compiled Python (a strict language)
# terminates where the compiled Y would diverge; in our weak-head interpreter it is an ordinary
# fixpoint just like Y.
Z: Builder = lam(lambda f: app(
    lam(lambda x: app(f, lam(lambda v: app(app(x, x), v)))),
    lam(lambda x: app(f, lam(lambda v: app(app(x, x), v)))),
))


def _scott(arity: int, tag: int, fields: "list[Builder]") -> Builder:
    """A Scott constructor over ``arity`` cases: select the ``tag``-th handler and apply the fields."""
    def collect(handlers: "list[Builder]") -> Builder:
        if len(handlers) == arity:
            applied = handlers[tag]
            for field in fields:
                applied = app(applied, field)
            return applied
        return lam(lambda handler: collect(handlers + [handler]))

    return collect([])


# Quoted source: three constructors (QVar/QLam/QApp).
def q_var(index: Builder) -> Builder:
    return _scott(3, 0, [index])


def q_lam(body: Builder) -> Builder:
    return _scott(3, 1, [body])


def q_app(function: Builder, argument: Builder) -> Builder:
    return _scott(3, 2, [function, argument])


# Quoted Python expression: five constructors (PyVar/PyLam/PyApp/PyForce/PyThunk).
def _py_var(level: Builder) -> Builder:
    return _scott(5, 0, [level])


def _py_lam(level: Builder, body: Builder) -> Builder:
    return _scott(5, 1, [level, body])


def _py_app(function: Builder, argument: Builder) -> Builder:
    return _scott(5, 2, [function, argument])


def _py_force(expr: Builder) -> Builder:
    return _scott(5, 3, [expr])


def _py_thunk(expr: Builder) -> Builder:
    return _scott(5, 4, [expr])


# sub a b = a - b, by applying PRED to a, b times.
_SUB: Builder = lam(lambda a: lam(lambda b: app(app(b, PRED), a)))

# Target wrappers, selected by the option (a Church boolean ``thunked``): the lazy target wraps a
# variable and a function in PyForce and an argument in PyThunk; the eager target wraps with identity.
_FORCE_WRAP: Builder = lam(lambda expr: _py_force(expr))
_THUNK_WRAP: Builder = lam(lambda expr: _py_thunk(expr))
_IDENTITY_WRAP: Builder = lam(lambda expr: expr)


def _select_wrap(thunked: Builder, lazy_wrap: Builder) -> Builder:
    # thunked is a Church boolean: it picks lazy_wrap when lazy (TRUE), identity when eager (FALSE).
    return app(app(thunked, lazy_wrap), _IDENTITY_WRAP)


# COMPILE = lambda thunked. Z (lambda self. lambda d. lambda q.
#   q (lambda i. wrapVar (PyVar (sub d (succ i))))                    -- QVar i
#     (lambda b. PyLam d (self (succ d) b))                          -- QLam b
#     (lambda f. lambda a. PyApp (wrapFun (self d f)) (wrapArg (self d a))))  -- QApp f a
# wrapVar = wrapFun = (thunked ? PyForce : id); wrapArg = (thunked ? PyThunk : id).
COMPILE: Builder = lam(lambda thunked: app(
    Z,
    lam(lambda self_recursion: lam(lambda depth: lam(lambda quoted: app(app(app(
        quoted,
        lam(lambda index: app(
            _select_wrap(thunked, _FORCE_WRAP),
            _py_var(app(app(_SUB, depth), app(SUCC, index))),
        )),
        ),
        lam(lambda body: _py_lam(depth, app(app(self_recursion, app(SUCC, depth)), body))),
        ),
        lam(lambda function: lam(lambda argument: _py_app(
            app(_select_wrap(thunked, _FORCE_WRAP), app(app(self_recursion, depth), function)),
            app(_select_wrap(thunked, _THUNK_WRAP), app(app(self_recursion, depth), argument)),
        ))),
    )))),
))


def quote(node: Node) -> Builder:
    """Reflect an interpreter lambda ``Node`` into a quoted-lambda Scott source term."""
    match node:
        case Var(index=index):
            return q_var(church(index))
        case Lam(body=body):
            return q_lam(quote(body))
        case App(function=function, argument=argument):
            return q_app(quote(function), quote(argument))
        case _:
            raise ValueError(f"cannot quote {node!r}")


class Runtime(Enum):
    CALL_BY_VALUE = auto()  # strict: an argument is evaluated to a value before the call
    CALL_BY_NAME = auto()  # an argument is a thunk recomputed on each force (no sharing)
    CALL_BY_NEED = auto()  # call-by-name plus memoisation: the thunk computes once and shares
    INTERPRET = auto()  # not a compiled target: re-submit the term to the interpreter


def _option(runtime: Runtime) -> Builder:
    """The Scott compilation option for a compiled target: a Church boolean ``thunked``."""
    if runtime is Runtime.CALL_BY_VALUE:
        return FALSE
    if runtime is Runtime.CALL_BY_NAME:
        return TRUE
    if runtime is Runtime.CALL_BY_NEED:
        raise NotImplementedError("call-by-need codegen (explicit memoising thunks) is not built yet")
    raise ValueError("the interpret target is not compiled; compile call-by-value or call-by-name")


def compile_quoted(option: Builder, quoted: Builder) -> Node:
    """Run ``COMPILE`` (at the given option) on a quoted source term, returning the Scott Python expr."""
    return build(app(app(app(COMPILE, option), church(0)), quoted))


def _arguments(name: str) -> ast.arguments:
    return ast.arguments(
        posonlyargs=[], args=[ast.arg(arg=name)], kwonlyargs=[], kw_defaults=[], defaults=[],
    )


def _no_args() -> ast.arguments:
    return ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[])


def _decode_pyast(node: Node) -> ast.expr:
    """Decode a Scott Python expression (PyVar/PyLam/PyApp/PyForce/PyThunk) to a real ``ast`` node.

    This is generic: the target-specific shape (force/thunk wrapping) was decided by the lambda term,
    so the decoder just renders each constructor, with no target branching.
    """
    tag, fields = _extract(node, (1, 2, 2, 1, 1), _PY_BASE)
    match tag:
        case 0:  # PyVar level
            return ast.Name(id=f"v{_church_to_int(fields[0])}", ctx=ast.Load())
        case 1:  # PyLam level body
            return ast.Lambda(args=_arguments(f"v{_church_to_int(fields[0])}"), body=_decode_pyast(fields[1]))
        case 2:  # PyApp function argument
            return ast.Call(func=_decode_pyast(fields[0]), args=[_decode_pyast(fields[1])], keywords=[])
        case 3:  # PyForce expr -> force(expr)
            return ast.Call(
                func=ast.Name(id="force", ctx=ast.Load()), args=[_decode_pyast(fields[0])], keywords=[],
            )
        case 4:  # PyThunk expr -> Thunk(lambda: expr)
            return ast.Call(
                func=ast.Name(id="Thunk", ctx=ast.Load()),
                args=[ast.Lambda(args=_no_args(), body=_decode_pyast(fields[0]))],
                keywords=[],
            )
        case _:
            raise ValueError(f"unknown PyExpr tag {tag}")


# --- runtime support for the compiled call-by-name target ---------------------------------------
# The call-by-name target's emitted Python refers to the free names ``force`` and ``Thunk``. An
# argument is a thunk ``Thunk(lambda: a)`` recomputed on each ``force``, matching the interpreter's
# weak-head reduction so every normalizing term computes its value. (The call-by-value target is
# strict and self-contained; the interpret target is the interpreter, not a compiled runtime.)


class _Thunk:
    """A delayed computation; ``force`` evaluates it."""

    __slots__ = ("_fn", "__dict__")

    def __init__(self, fn) -> None:
        self._fn = fn


class _LazyThunk(_Thunk):
    @property
    def value(self):
        return self._fn()  # call-by-name: recompute on every force


def force(value):
    return value.value if isinstance(value, _Thunk) else value


def runtime_globals(runtime: Runtime) -> dict:
    """The evaluation globals for a compiled program under the given runtime.

    Call-by-value source is self-contained; call-by-name source needs ``force`` and the
    recompute-on-force ``Thunk``.
    """
    if runtime is Runtime.CALL_BY_VALUE:
        return {}
    if runtime is Runtime.CALL_BY_NAME:
        return {"force": force, "Thunk": _LazyThunk}
    if runtime is Runtime.CALL_BY_NEED:
        return call_by_need_globals()
    raise ValueError("the interpret target is interpreted; it has no compiled runtime globals")


def compile_to_source(node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile an interpreter lambda term to Python source for the given compiled target.

    Call-by-value yields a strict expression; call-by-name yields the expression with the lambda
    term's ``force``/``Thunk`` wrapping. The interpret target is interpreted, not compiled.
    """
    if runtime is Runtime.CALL_BY_NEED:
        return _compile_need_source(node)
    compiled = compile_quoted(_option(runtime), quote(node))
    return ast.unparse(ast.fix_missing_locations(_decode_pyast(compiled)))


# --- the interpret target: emit Python that re-submits the term to the interpreter ---------------
# A term the analysis does not certify for a compiled target keeps the interpreter. Its compiled
# Python is an ``interpret(...)`` call whose argument reconstructs the term as an interpreter ``Node``
# with ``make_var`` / ``make_lam`` / ``make_app`` (the interning constructors), so the emitted source
# is self-contained text given the four names in ``interpret_globals``. ``interpret`` hands the node
# to the interpreter; the node is the value, normalized lazily when the result is observed. This is
# the head of a specialized program: a by-value-certified subgraph compiles inline, the rest reads
# ``interpret(...)``.


def _node_to_ast(node: Node) -> ast.expr:
    """Reconstruct ``node`` as Python that rebuilds the interpreter ``Node`` with ``make_*``."""
    match node:
        case Var(index=index):
            return ast.Call(
                func=ast.Name(id="make_var", ctx=ast.Load()),
                args=[ast.Constant(value=index)], keywords=[],
            )
        case Lam(body=body):
            return ast.Call(
                func=ast.Name(id="make_lam", ctx=ast.Load()), args=[_node_to_ast(body)], keywords=[],
            )
        case App(function=function, argument=argument):
            return ast.Call(
                func=ast.Name(id="make_app", ctx=ast.Load()),
                args=[_node_to_ast(function), _node_to_ast(argument)], keywords=[],
            )
        case _:
            raise ValueError(f"cannot reconstruct {node!r}")


def interpret(node: Node) -> Node:
    """The interpret boundary: a reconstructed term handed back to the interpreter.

    The node is the value; the interpreter computes its weak head normal form lazily when the result
    is observed (decoded, rendered, or applied at the node level). This is the runtime hook a compiled
    by-value island is spliced around in a specialized program.
    """
    return node


def interpret_globals() -> dict:
    """The evaluation globals for interpret-headed source: the node constructors and ``interpret``."""
    return {"make_var": make_var, "make_lam": make_lam, "make_app": make_app, "interpret": interpret}


def compile_interpreted(node: Node) -> str:
    """Compile ``node`` to interpret-headed Python: ``interpret(<node reconstructed with make_*>)``."""
    call = ast.Call(
        func=ast.Name(id="interpret", ctx=ast.Load()), args=[_node_to_ast(node)], keywords=[],
    )
    return ast.unparse(ast.fix_missing_locations(call))


def compile_with_interpreted(compiler_node: Node, node: Node, runtime: Runtime = Runtime.CALL_BY_VALUE) -> str:
    """Compile ``node`` with an interpret-headed compiler, a ``COMPILE`` ``Node`` run by the interpreter.

    ``compiler_node`` is what ``compile_interpreted(build(COMPILE))`` evaluates to: the compiler itself,
    handed back to the interpreter. The interpreter applies it to the option, depth ``0``, and the
    quoted program, and the resulting Scott Python AST is reified by the same ``_decode_pyast`` boundary
    the in-process compiler uses. So the self-hosted compiler, compiled to interpret-headed Python,
    compiles any program to the same source as ``compile_to_source``: the bootstrap through the
    interpret target.
    """
    applied = make_app(
        make_app(make_app(compiler_node, build(_option(runtime))), build(church(0))),
        build(quote(node)),
    )
    return ast.unparse(ast.fix_missing_locations(_decode_pyast(applied)))


# --- call-by-need: explicit memoising thunks, emitted entirely by the COMPILE_NEED lambda term ---
# Call-by-need adds sharing to call-by-name: a thunk computes once and caches. The cache and its
# update need statements, so the target is statement-based, and the WHOLE structure (the def, the
# nonlocal, the sentinel guard, the assignment, the return, the module wrapper) is emitted by the
# COMPILE_NEED lambda term as a Scott-encoded Python AST. Python only decodes that AST 1:1; it
# assembles nothing. Every sub-term compiles to a memoising thunk of the shape the design fixed:
#
#     v_<cell> = CALL_BY_NEED_SENTINEL
#     def v_<thunk>():
#         nonlocal v_<cell>
#         if v_<cell> is CALL_BY_NEED_SENTINEL:
#             <compute statements>
#             v_<cell> = <compute expression>
#         return v_<cell>
#
# Forcing a thunk is calling it; a bound variable arrives as a thunk and is forced on use; a lambda's
# value is an inner ``def v_<func>(v_<param>)``. Every identifier is a SYMBOL: the path of the AST
# node it belongs to, a list of Church-numeral segments (a branch index per descent, plus a kind tag),
# decoded to an underscore-joined name like ``v_0_2_1`` that is unique by construction. A binder's
# symbol is threaded down in an environment so a variable looks up its binder's name by de Bruijn
# index. The program is wrapped in ``def _program(): ...; return <root thunk>`` so the ``nonlocal``
# cells have an enclosing function scope, and ``program = _program()`` binds it.

# Path segments: a branch index per descent (function/argument/lambda-body) and a kind tag per role.
_BRANCH_FUNCTION: Builder = church(0)
_BRANCH_ARGUMENT: Builder = church(1)
_BRANCH_BODY: Builder = church(2)
_KIND_THUNK: Builder = church(0)
_KIND_CELL: Builder = church(1)
_KIND_FUNCTION: Builder = church(2)
_KIND_VARIABLE: Builder = church(3)


def _let(value: Builder, body: "object") -> Builder:
    """Bind ``value`` for ``body`` (a Python ``lambda`` over the bound Builder)."""
    return app(lam(body), value)


def _one(element: Builder) -> Builder:
    return cons(element, SCOTT_NIL)


def _two(first: Builder, second: Builder) -> Builder:
    return cons(first, cons(second, SCOTT_NIL))


# append xs ys = xs (lambda h. lambda t. cons h (self t ys)) ys, by Scott-list elimination.
_APPEND: Builder = app(Z, lam(lambda self_recursion: lam(lambda xs: lam(lambda ys: app(
    app(xs, lam(lambda head: lam(lambda tail: cons(head, app(app(self_recursion, tail), ys))))),
    ys,
)))))


def _append(xs: Builder, ys: Builder) -> Builder:
    return app(app(_APPEND, xs), ys)


# tail/head by Scott-list elimination; nth drops ``index`` heads (Church iteration) then takes head.
_TAIL: Builder = lam(lambda lst: app(app(lst, lam(lambda head: lam(lambda tail: tail))), SCOTT_NIL))
_HEAD: Builder = lam(lambda lst: app(app(lst, lam(lambda head: lam(lambda tail: head))), SCOTT_NIL))
_NTH: Builder = lam(lambda index: lam(lambda env: app(_HEAD, app(app(index, _TAIL), env))))


# A compiled (sub)term is a Scott pair of its setup statements and its value expression.
def _need_pair(setup: Builder, value: Builder) -> Builder:
    return lam(lambda selector: app(app(selector, setup), value))


def _fst(pair: Builder) -> Builder:
    return app(pair, TRUE)


def _snd(pair: Builder) -> Builder:
    return app(pair, FALSE)


# Scott Python AST constructors (the lambda term builds these; the decoder maps each 1:1 to ``ast``).
# A symbol names an identifier: a path (list of Church segments) rendered ``v_<seg>_<seg>...``, or one
# of the two fixed wrapper names.
def _sym_path(path: Builder) -> Builder:
    return _scott(3, 0, [path])


_SYM_PROGRAM_DEF: Builder = _scott(3, 1, [])  # the wrapper function name ``_program``
_SYM_PROGRAM_BIND: Builder = _scott(3, 2, [])  # the bound result name ``program``


def _name_symbol(kind: Builder, path: Builder) -> Builder:
    """The symbol naming the ``kind`` identifier of the node at ``path`` (kind tag is the path head)."""
    return _sym_path(cons(kind, path))


# Expressions.
def _ex_name(symbol: Builder) -> Builder:
    return _scott(5, 0, [symbol])


_EX_SENTINEL: Builder = _scott(5, 1, [])  # the CALL_BY_NEED_SENTINEL name


def _ex_force(expr: Builder) -> Builder:
    return _scott(5, 2, [expr])  # expr()


def _ex_app(function: Builder, argument: Builder) -> Builder:
    return _scott(5, 3, [function, argument])  # function(argument)


def _ex_is(left: Builder, right: Builder) -> Builder:
    return _scott(5, 4, [left, right])  # left is right


# Statements.
def _st_func_def(name: Builder, parameters: Builder, body: Builder) -> Builder:
    return _scott(5, 0, [name, parameters, body])


def _st_nonlocal(names: Builder) -> Builder:
    return _scott(5, 1, [names])


def _st_if(test: Builder, body: Builder) -> Builder:
    return _scott(5, 2, [test, body])


def _st_assign(target: Builder, value: Builder) -> Builder:
    return _scott(5, 3, [target, value])


def _st_return(value: Builder) -> Builder:
    return _scott(5, 4, [value])


def _thunk_scaffold(cell: Builder, thunk: Builder, compute: Builder) -> Builder:
    """The two setup statements introducing a memoising thunk: the cell init and the def."""
    body = cons(
        _st_nonlocal(_one(cell)),
        cons(
            _st_if(_ex_is(_ex_name(cell), _EX_SENTINEL), compute),
            _one(_st_return(_ex_name(cell))),
        ),
    )
    return _two(_st_assign(cell, _EX_SENTINEL), _st_func_def(thunk, SCOTT_NIL, body))


# The recursion: self path env quoted -> (setup statements, value expression). ``path`` is the AST
# address (Church segments, innermost first); ``env`` is the list of in-scope binder symbols.
_COMPILE_NEED_REC: Builder = app(Z, lam(lambda self_recursion: lam(lambda path: lam(lambda env: lam(
    lambda quoted: app(app(app(
        quoted,
        # QVar index: the variable is its binder's thunk, looked up by de Bruijn index; no setup.
        lam(lambda index: _need_pair(SCOTT_NIL, _ex_name(app(app(_NTH, index), env)))),
        ),
        # QLam body: the value is an inner function; wrap it in a memoising thunk.
        lam(lambda body: _let(
            _name_symbol(_KIND_VARIABLE, path),
            lambda parameter: _let(
                app(app(app(self_recursion, cons(_BRANCH_BODY, path)), cons(parameter, env)), body),
                lambda compiled_body: _need_pair(
                    _thunk_scaffold(
                        _name_symbol(_KIND_CELL, path),
                        _name_symbol(_KIND_THUNK, path),
                        _two(
                            _st_func_def(
                                _name_symbol(_KIND_FUNCTION, path),
                                _one(parameter),
                                _append(_fst(compiled_body), _one(_st_return(_snd(compiled_body)))),
                            ),
                            _st_assign(
                                _name_symbol(_KIND_CELL, path),
                                _ex_name(_name_symbol(_KIND_FUNCTION, path)),
                            ),
                        ),
                    ),
                    _ex_name(_name_symbol(_KIND_THUNK, path)),
                ),
            ),
        )),
        ),
        # QApp f a: force the function and apply the argument thunk; the result is a memoising thunk.
        lam(lambda function: lam(lambda argument: _let(
            app(app(app(self_recursion, cons(_BRANCH_FUNCTION, path)), env), function),
            lambda compiled_function: _let(
                app(app(app(self_recursion, cons(_BRANCH_ARGUMENT, path)), env), argument),
                lambda compiled_argument: _need_pair(
                    _thunk_scaffold(
                        _name_symbol(_KIND_CELL, path),
                        _name_symbol(_KIND_THUNK, path),
                        _append(
                            _fst(compiled_function),
                            _append(
                                _fst(compiled_argument),
                                _one(_st_assign(
                                    _name_symbol(_KIND_CELL, path),
                                    # Force to WHNF: applying the function returns the body thunk, which
                                    # must itself be forced so this cell holds a value, not a thunk.
                                    _ex_force(_ex_app(
                                        _ex_force(_snd(compiled_function)), _snd(compiled_argument),
                                    )),
                                )),
                            ),
                        ),
                    ),
                    _ex_name(_name_symbol(_KIND_THUNK, path)),
                ),
            ),
        ))),
    ))))))


# COMPILE_NEED wraps the root's (statements, value) in def _program(): ...; return value, then
# program = _program(), so the nonlocal cells have an enclosing function scope.
COMPILE_NEED: Builder = lam(lambda quoted: _let(
    app(app(app(_COMPILE_NEED_REC, SCOTT_NIL), SCOTT_NIL), quoted),
    lambda root: _two(
        _st_func_def(
            _SYM_PROGRAM_DEF, SCOTT_NIL, _append(_fst(root), _one(_st_return(_snd(root)))),
        ),
        _st_assign(_SYM_PROGRAM_BIND, _ex_force(_ex_name(_SYM_PROGRAM_DEF))),
    ),
))


_NEED_SYM_BASE = 6_000_000
_NEED_EXPR_BASE = 6_500_000
_NEED_STMT_BASE = 7_200_000

_SENTINEL_NAME = "CALL_BY_NEED_SENTINEL"


def _decode_symbol(node: Node) -> str:
    tag, fields = _extract(node, (1, 0, 0), _NEED_SYM_BASE)
    match tag:
        case 0:  # a path symbol: v_<seg>_<seg>...
            segments = [_church_to_int(segment) for segment in _decode_scott_list(fields[0])]
            return "_".join(["v", *(str(segment) for segment in segments)])
        case 1:
            return "_program"
        case 2:
            return "program"
        case _:
            raise ValueError(f"unknown call-by-need symbol tag {tag}")


def _decode_need_expr(node: Node) -> ast.expr:
    tag, fields = _extract(node, (1, 0, 1, 2, 2), _NEED_EXPR_BASE)
    match tag:
        case 0:  # a name
            return ast.Name(id=_decode_symbol(fields[0]), ctx=ast.Load())
        case 1:  # the sentinel name
            return ast.Name(id=_SENTINEL_NAME, ctx=ast.Load())
        case 2:  # force: expr()
            return ast.Call(func=_decode_need_expr(fields[0]), args=[], keywords=[])
        case 3:  # function(argument)
            return ast.Call(
                func=_decode_need_expr(fields[0]), args=[_decode_need_expr(fields[1])], keywords=[],
            )
        case 4:  # left is right
            return ast.Compare(
                left=_decode_need_expr(fields[0]), ops=[ast.Is()],
                comparators=[_decode_need_expr(fields[1])],
            )
        case _:
            raise ValueError(f"unknown call-by-need expression tag {tag}")


def _decode_need_statements(node: Node) -> "list[ast.stmt]":
    return [_decode_need_statement(element) for element in _decode_scott_list(node)]


def _decode_need_statement(node: Node) -> ast.stmt:
    tag, fields = _extract(node, (3, 1, 2, 2, 1), _NEED_STMT_BASE)
    match tag:
        case 0:  # a function def
            parameters = [_decode_symbol(parameter) for parameter in _decode_scott_list(fields[1])]
            arguments = _arguments(*parameters) if parameters else _no_args()
            return ast.FunctionDef(
                name=_decode_symbol(fields[0]), args=arguments,
                body=_decode_need_statements(fields[2]), decorator_list=[],
            )
        case 1:  # nonlocal names
            return ast.Nonlocal(names=[_decode_symbol(name) for name in _decode_scott_list(fields[0])])
        case 2:  # if test: body  (no else)
            return ast.If(
                test=_decode_need_expr(fields[0]), body=_decode_need_statements(fields[1]), orelse=[],
            )
        case 3:  # target = value
            return ast.Assign(
                targets=[ast.Name(id=_decode_symbol(fields[0]), ctx=ast.Store())],
                value=_decode_need_expr(fields[1]),
            )
        case 4:  # return value
            return ast.Return(value=_decode_need_expr(fields[0]))
        case _:
            raise ValueError(f"unknown call-by-need statement tag {tag}")


def _decode_need_module(node: Node) -> ast.Module:
    """Decode the call-by-need top-level statement list (built by COMPILE_NEED) to an ``ast.Module``."""
    return ast.Module(body=_decode_need_statements(node), type_ignores=[])


class _CallByNeedSentinel:
    """The unforced marker stored in a memo cell before its thunk computes."""

    def __repr__(self) -> str:
        return _SENTINEL_NAME


def call_by_need_globals() -> dict:
    """The evaluation globals for a call-by-need program: just the unforced-cell sentinel.

    Forcing is calling a thunk, so there is no ``force`` helper; the emitted module is self-contained
    apart from the sentinel its memo cells compare against.
    """
    return {_SENTINEL_NAME: _CallByNeedSentinel()}


def _compile_need_source(node: Node) -> str:
    """Compile a term to the call-by-need module source (explicit memoising thunks)."""
    module = build(app(COMPILE_NEED, quote(node)))
    return ast.unparse(ast.fix_missing_locations(_decode_need_module(module)))


# --- bootstrap: the self-compiled compiler, run through the interpret target --------------------
# COMPILE compiled in specialized mode is interpret-headed (COMPILE is untypable: its Z fixpoint
# self-applies), so the self-hosted compiler is the COMPILE node handed back to the interpreter.
# ``compiled_compiler`` evaluates that interpret-headed source to the node; ``compile_with_interpreted``
# runs it as a compiler, reifying the Scott Python-AST result through ``_decode_pyast``, the same
# boundary the in-process compiler uses. So the compiler compiled by itself, through interpret, is a
# working compiler agreeing with ``compile_to_source``.


def compiled_compiler() -> Node:
    """The self-compiled compiler: COMPILE compiled to interpret-headed Python, evaluated to its node."""
    return eval(compile_interpreted(build(COMPILE)), interpret_globals())
