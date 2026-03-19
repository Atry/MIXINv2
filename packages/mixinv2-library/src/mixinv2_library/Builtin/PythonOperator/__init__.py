"""All Python operator module FFI wrappers, generated programmatically.

Covers every public function in Python's operator module:
- Binary (operand0, operand1 -> result): arithmetic, comparison, bitwise, sequence
- Unary (operand -> result): neg, pos, abs, invert, not_, truth, index
- In-place (operand0, operand1 -> result): iadd, isub, etc. (mutate + return)
- Ternary (target, key, value -> result): setitem
- Higher-order (target + params -> result): attrgetter, itemgetter, methodcaller, call
- Special: length_hint, delitem
"""

import operator

from mixinv2 import extern, public, resource
from mixinv2._core import MappingScopeDefinition


def _make_binary_operator(operation):
    @extern
    def operand0() -> object: ...

    @extern
    def operand1() -> object: ...

    @public
    @resource
    def result(operand0: object, operand1: object) -> object:
        return operation(operand0, operand1)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"operand0": operand0, "operand1": operand1, "result": result},
    )


def _make_unary_operator(operation):
    @extern
    def operand() -> object: ...

    @public
    @resource
    def result(operand: object) -> object:
        return operation(operand)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"operand": operand, "result": result},
    )


# --- Binary operators (operand0, operand1 -> result) ---
_BINARY_OPERATORS = {
    # Arithmetic
    "Add": operator.add,
    "Subtract": operator.sub,
    "Multiply": operator.mul,
    "TrueDivide": operator.truediv,
    "FloorDivide": operator.floordiv,
    "Modulo": operator.mod,
    "Power": operator.pow,
    "MatrixMultiply": operator.matmul,
    # Comparison
    "Equal": operator.eq,
    "NotEqual": operator.ne,
    "LessThan": operator.lt,
    "LessThanOrEqual": operator.le,
    "GreaterThan": operator.gt,
    "GreaterThanOrEqual": operator.ge,
    "Is": operator.is_,
    "IsNot": operator.is_not,
    # Bitwise
    "BitwiseAnd": operator.and_,
    "BitwiseOr": operator.or_,
    "BitwiseXor": operator.xor,
    "LeftShift": operator.lshift,
    "RightShift": operator.rshift,
    # Sequence
    "Concatenate": operator.concat,
    "Contains": operator.contains,
    "GetItem": operator.getitem,
    "CountOf": operator.countOf,
    "IndexOf": operator.indexOf,
}

# --- Unary operators (operand -> result) ---
_UNARY_OPERATORS = {
    "Negate": operator.neg,
    "Positive": operator.pos,
    "Absolute": operator.abs,
    "BitwiseInvert": operator.invert,
    "Invert": operator.inv,
    "LogicalNot": operator.not_,
    "Truth": operator.truth,
    "Index": operator.index,
}

# --- In-place operators (operand0, operand1 -> result) ---
_INPLACE_OPERATORS = {
    "InplaceAdd": operator.iadd,
    "InplaceSubtract": operator.isub,
    "InplaceMultiply": operator.imul,
    "InplaceTrueDivide": operator.itruediv,
    "InplaceFloorDivide": operator.ifloordiv,
    "InplaceModulo": operator.imod,
    "InplacePower": operator.ipow,
    "InplaceMatrixMultiply": operator.imatmul,
    "InplaceBitwiseAnd": operator.iand,
    "InplaceBitwiseOr": operator.ior,
    "InplaceBitwiseXor": operator.ixor,
    "InplaceLeftShift": operator.ilshift,
    "InplaceRightShift": operator.irshift,
    "InplaceConcatenate": operator.iconcat,
}

for _name, _operation in _BINARY_OPERATORS.items():
    globals()[_name] = _make_binary_operator(_operation)

for _name, _operation in _UNARY_OPERATORS.items():
    globals()[_name] = _make_unary_operator(_operation)

for _name, _operation in _INPLACE_OPERATORS.items():
    globals()[_name] = _make_binary_operator(_operation)


# --- Special operators (hand-written, unique signatures) ---


def _make_set_item():
    """operator.setitem(target, key, value) -> None"""

    @extern
    def target() -> object: ...

    @extern
    def key() -> object: ...

    @extern
    def value() -> object: ...

    @public
    @resource
    def result(target: object, key: object, value: object) -> None:
        operator.setitem(target, key, value)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"target": target, "key": key, "value": value, "result": result},
    )


SetItem = _make_set_item()


def _make_delete_item():
    """operator.delitem(target, key) -> None"""

    @extern
    def target() -> object: ...

    @extern
    def key() -> object: ...

    @public
    @resource
    def result(target: object, key: object) -> None:
        operator.delitem(target, key)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"target": target, "key": key, "result": result},
    )


DeleteItem = _make_delete_item()


def _make_length_hint():
    """operator.length_hint(target) -> result"""

    @extern
    def target() -> object: ...

    @public
    @resource
    def result(target: object) -> int:
        return operator.length_hint(target)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"target": target, "result": result},
    )


LengthHint = _make_length_hint()


def _make_call():
    """operator.call(target, *arguments) -> result"""

    @extern
    def target() -> object: ...

    @extern
    def arguments() -> tuple: ...

    @public
    @resource
    def result(target: object, arguments: tuple) -> object:
        return operator.call(target, *arguments)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"target": target, "arguments": arguments, "result": result},
    )


Call = _make_call()


def _make_method_call():
    """operator.methodcaller(methodName, *arguments)(target) -> result"""

    @extern
    def target() -> object: ...

    @extern
    def methodName() -> str: ...

    @extern
    def arguments() -> tuple: ...

    @public
    @resource
    def result(target: object, methodName: str, arguments: tuple) -> object:
        return operator.methodcaller(methodName, *arguments)(target)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={
            "target": target,
            "methodName": methodName,
            "arguments": arguments,
            "result": result,
        },
    )


MethodCall = _make_method_call()


def _make_attribute_get():
    """operator.attrgetter(attributeName)(target) -> result"""

    @extern
    def target() -> object: ...

    @extern
    def attributeName() -> str: ...

    @public
    @resource
    def result(target: object, attributeName: str) -> object:
        return operator.attrgetter(attributeName)(target)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={
            "target": target,
            "attributeName": attributeName,
            "result": result,
        },
    )


AttributeGet = _make_attribute_get()


def _make_item_get():
    """operator.itemgetter(key)(target) -> result"""

    @extern
    def target() -> object: ...

    @extern
    def key() -> object: ...

    @public
    @resource
    def result(target: object, key: object) -> object:
        return operator.itemgetter(key)(target)

    return MappingScopeDefinition(
        inherits=(),
        is_public=True,
        underlying={"target": target, "key": key, "result": result},
    )


ItemGet = _make_item_get()
