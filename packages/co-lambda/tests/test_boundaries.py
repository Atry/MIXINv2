"""The bootstrap-honesty gates: pure-lambda module purity and the closed runtime API.

Two boundaries keep the bootstrap claim honest. (1) The compiler-source modules are pure lambda
calculus: every top-level binding is a Builder, the only ``def`` form allowed is a ``@curry``
decorated one (which IS a Builder, an object-level abstraction), and the imports stay within the
notation/codec/lambda layers (no runtime, no operational stdlib). (2) The runtime vocabulary is the
declared ``RUNTIME_API``: a generated program's free names must be members, so the runtime cannot
grow ad hoc at an emission site.
"""

from __future__ import annotations

import ast
import builtins
import importlib
from pathlib import Path

from co_lambda._dsl import app, build
from co_lambda._examples import FINITE_LIST
from co_lambda._prelude import FACTORIAL, KESTREL, MULT, PLUS
from co_lambda._codec import church
from co_lambda._runtime import RUNTIME_API, runnable_module
from co_lambda._specialize import Runtime, SpecializedOption, WholeOption, compile

_LAMBDA_SOURCE_MODULES = (
    "_prelude",
    "_binnat",
    "_analysis",
    "_typecheck",
    "_reduce",
    "_compiler",
    "_compile_term",
    "_imperative",
)

# The layers a pure-lambda module may import from: the HOAS notation, the shared sugar, the
# emission notation, codec literal renderings, and other lambda-source modules. Nothing operational.
_ALLOWED_IMPORT_MODULES = frozenset(
    {"__future__", "co_lambda._dsl", "co_lambda._sugar", "co_lambda._pybuild", "co_lambda._codec"}
    | {f"co_lambda.{name}" for name in _LAMBDA_SOURCE_MODULES}
)


def _module_path(name: str) -> Path:
    module = importlib.import_module(f"co_lambda.{name}")
    file = module.__file__
    assert file is not None
    return Path(file)


def test_lambda_source_modules_are_pure() -> None:
    # Every top-level statement is a Builder assignment, a @curry def (itself a Builder), an
    # allowed import, or a docstring; no class, no plain def, no operational statement.
    for name in _LAMBDA_SOURCE_MODULES:
        tree = ast.parse(_module_path(name).read_text())
        for node in tree.body:
            match node:
                case ast.ImportFrom(module=module):
                    assert module in _ALLOWED_IMPORT_MODULES, (
                        f"{name} imports {module}, outside the pure-lambda allowance"
                    )
                case ast.Import():
                    raise AssertionError(f"{name} uses a plain import, outside the pure-lambda allowance")
                case ast.FunctionDef(decorator_list=decorators):
                    assert any(
                        isinstance(decorator, ast.Name) and decorator.id == "curry"
                        for decorator in decorators
                    ), f"{name}.{node.name} is a def without @curry (not a lambda-term binding)"
                case ast.AnnAssign() | ast.Assign():
                    pass  # a Builder constant
                case ast.Expr(value=ast.Constant()):
                    pass  # the docstring or a bare string section header
                case _:
                    raise AssertionError(
                        f"{name} contains a non-lambda top-level statement: {ast.dump(node)[:80]}"
                    )


def _free_names(source: str) -> set[str]:
    module = ast.parse(source)
    loaded: set[str] = set()
    bound: set[str] = set()
    for node in ast.walk(module):
        match node:
            case ast.Name(id=identifier, ctx=ast.Load()):
                loaded.add(identifier)
            case ast.Name(id=identifier):
                bound.add(identifier)
            case ast.arg(arg=identifier):
                bound.add(identifier)
            case ast.FunctionDef(name=identifier):
                bound.add(identifier)
            case ast.alias(name=identifier, asname=alias):
                bound.add(alias if alias is not None else identifier.split(".")[0])
            case _:
                pass
    return loaded - bound - set(dir(builtins))


def test_generated_programs_reference_only_the_runtime_api() -> None:
    # Representative programs across every target; each emitted module's free names must be members
    # of the declared RUNTIME_API (the runnable header itself binds only API names).
    api_names = set(RUNTIME_API)
    specialized = compile(build(app(FACTORIAL, church(3))), SpecializedOption(8))
    whole_value = compile(build(app(app(PLUS, church(2)), church(3))), WholeOption(Runtime.CALL_BY_VALUE))
    whole_name = compile(build(KESTREL), WholeOption(Runtime.CALL_BY_NAME))
    whole_need = compile(build(app(app(MULT, church(2)), church(3))), WholeOption(Runtime.CALL_BY_NEED))
    for source in (specialized, runnable_module(specialized), whole_value, whole_name, whole_need):
        assert _free_names(source) <= api_names, (
            f"generated code references names outside RUNTIME_API: {_free_names(source) - api_names}"
        )
    assert FINITE_LIST is not None  # the examples module stays importable (boundary data intact)
