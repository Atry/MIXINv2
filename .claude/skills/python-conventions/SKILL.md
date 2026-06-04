---
name: python-conventions
description: "Python coding conventions for this project (mandatory @dataclass with kw_only/slots/frozen/weakref_slot, @final + slots rules, no __all__/re-exports, no default values, @cached_property over __post_init__, tuple over list, comprehensions over append, self-descriptive names, @override + super(), and the Xxx | XxxSentinel pattern instead of Optional/None). Use whenever writing or editing Python (.py) code in this repository, or designing data structures, class hierarchies, or APIs in Python."
---

# Python Coding Conventions

### Use `@dataclass` for Structured Data

**Do NOT** use `tuple`, `NamedTuple`, `dict`, `TypedDict`, or custom `__init__` for structured data. Use `@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)` instead:

```python
# ✗ BAD - tuple (no field names, positional access only)
def get_user() -> tuple[int, str, str]:
    return (1, "alice", "alice@example.com")
id, name, email = get_user()  # Easy to mix up order

# ✗ BAD - NamedTuple (immutable, no methods, limited functionality)
from typing import NamedTuple
class User(NamedTuple):
    id: int
    name: str
    email: str

# ✗ BAD - dict (no type safety, typo-prone keys)
def get_user() -> dict[str, Any]:
    return {"id": 1, "name": "alice", "email": "alice@example.com"}

# ✗ BAD - TypedDict (dict with types, but still stringly-typed keys)
from typing import TypedDict
class User(TypedDict):
    id: int
    name: str
    email: str

# ✗ BAD - custom __init__
class User:
    def __init__(self, id: int, name: str, email: str):
        self.id = id
        self.name = name
        self.email = email

# ✓ GOOD - dataclass with full options
from dataclasses import dataclass

@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class User:
    id: int
    name: str
    email: str
```

**Why `@dataclass` over alternatives:**
- **vs tuple**: Named fields, type hints, readable access (`user.name` vs `user[1]`)
- **vs NamedTuple**: Methods, `@cached_property`, inheritance, better tooling support
- **vs dict/TypedDict**: Attribute access, IDE autocomplete, no string key typos
- **vs custom `__init__`**: Less boilerplate, automatic `__repr__`, `__eq__`, etc.

**Why `kw_only=True`:**
- Forces keyword arguments, making code more readable: `Config(name="x", value=1)`
- Prevents positional argument errors when adding/reordering fields
- Self-documenting at call sites

**Why `slots=True`:**
- Memory efficiency: no `__dict__` per instance
- Faster attribute access
- Prevents accidental attribute creation

**Why `frozen=True`:**
- Immutability by default: prevents accidental mutation
- Makes instances hashable (can be used as dict keys or in sets)
- Thread-safe without locks

**Why `weakref_slot=True`:**
- Allows weak references to instances even with `slots=True`
- Enables garbage collection of cyclic references

**Exception: `frozen=False` with Cache Slots**

When using `slots=True` fields as internal cache (set via `setattr` after construction), `frozen=False` is allowed. Non-cache fields MUST have `Final` type hints:

```python
@dataclass(kw_only=True, slots=True, weakref_slot=True, eq=False)
class CachedScope:
    symbol: Final["MixinSymbol"]  # Non-cache: use Final
    _cached_child: object = field(init=False)  # Cache: set via setattr
```

**Note on `Final` type hints:**

Frozen dataclasses (`frozen=True`) already enforce runtime immutability, so `Final` type hints could be omitted:

```python
# ✓ GOOD - frozen dataclass without Final (frozen already ensures immutability)
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Config:
    name: str
    value: int

# ✗ UNNECESSARY - Final is redundant with frozen=True
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Config:
    name: Final[str]  # Redundant: frozen already prevents mutation
    value: Final[int]
```

### `@final` and `slots` Requirements for Dataclasses

**Rule 1: Never instantiate non-`@final` dataclasses.**

Non-`@final` dataclasses are abstract base classes meant for inheritance only. Direct instantiation is prohibited.

```python
# ✗ BAD - instantiating a non-@final dataclass
@dataclass(kw_only=True, eq=False)
class _BaseNode(ABC):
    name: str

node = _BaseNode(name="test")  # FORBIDDEN: _BaseNode is not @final

# ✓ GOOD - only instantiate @final dataclasses
@final
@dataclass(kw_only=True, slots=True, weakref_slot=True, eq=False)
class LeafNode(_BaseNode):
    value: int

node = LeafNode(name="test", value=42)  # OK: LeafNode is @final
```

**Rule 2: All `@final` dataclasses MUST have `slots=True` and `weakref_slot=True`.**

```python
# ✗ BAD - @final dataclass without slots
@final
@dataclass(kw_only=True, frozen=True)
class Config:
    name: str

# ✓ GOOD - @final dataclass with slots=True and weakref_slot=True
@final
@dataclass(kw_only=True, slots=True, weakref_slot=True, frozen=True)
class Config:
    name: str
```

**Rule 3: All non-`@final` dataclasses MUST NOT have `slots=True` or `weakref_slot=True`.**

This is because Python's `__slots__` does not support multiple inheritance when both parent classes have non-empty slots. Non-`@final` dataclasses are meant to be inherited, and adding slots would cause `TypeError: multiple bases have instance lay-out conflict`.

```python
# ✗ BAD - non-@final dataclass with slots (will break multiple inheritance)
@dataclass(kw_only=True, slots=True, weakref_slot=True, eq=False)
class _BaseMapping(ABC):
    data: dict[str, Any]

# ✓ GOOD - non-@final dataclass without slots
@dataclass(kw_only=True, eq=False)
class _BaseMapping(ABC):
    data: dict[str, Any]
```

**Using `@cached_property` with slots:**

When a `@final` dataclass needs `@cached_property`, inherit from `HasDict`:

```python
# ✓ GOOD - @final dataclass with @cached_property inherits HasDict
@final
@dataclass(kw_only=True, slots=True, weakref_slot=True, eq=False)
class ComputedNode(HasDict, _BaseNode):
    raw_value: int

    @cached_property
    def computed_value(self) -> int:
        return self.raw_value * 2
```

For non-`@final` dataclasses that need `@cached_property` and will be combined with other classes via multiple inheritance, inherit from `HasDict` but omit `slots=True`:

```python
# ✓ GOOD - non-@final dataclass with @cached_property
@dataclass(kw_only=True, eq=False)
class _CachingBase(HasDict, ABC):
    source: str

    @cached_property
    def cached_result(self) -> bytes:
        return self.source.encode()
```

**Summary table:**

| Dataclass type | `@final` | `slots=True, weakref_slot=True` | Can instantiate? |
| -------------- | -------- | ------------------------------- | ---------------- |
| Concrete leaf  | Yes      | Required                        | Yes              |
| Abstract base  | No       | Forbidden                       | No               |


### Avoid `__all__` and Re-exports

**Do NOT** use `__all__` or re-export symbols from `__init__.py`. All imports MUST be direct and explicit:

```python
# ✗ BAD - re-exporting in __init__.py
# src/hpcnc/model/__init__.py
from hpcnc.model.loader import load_model
__all__ = ["load_model"]

# ✗ BAD - importing from package instead of module
from hpcnc.model import load_model

# ✓ GOOD - empty __init__.py (or only docstring)
# src/hpcnc/model/__init__.py
"""Model package."""

# ✓ GOOD - direct import from module
from hpcnc.model.loader import load_model
```

**Why avoid `__all__` and re-exports:**
- Better grep-ability and "find usages" accuracy
- Clearer dependency graph
- Avoids circular import issues common with `__init__.py` re-exports
- Makes it explicit where a symbol is actually defined
- Reduced boilerplate in `__init__.py` files

### Avoid Default Values - They Are Anti-patterns

**Do NOT** use default values for dataclass fields or function parameters unless the user explicitly requests it:

```python
# ✗ BAD - default values hide required parameters
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Config:
    name: str
    value: int = 0  # BAD: default value
    role: str = "user"  # BAD: default value

def save_state(data: bytes, role: str = "ai") -> None:  # BAD: default value
    ...

# ✓ GOOD - all parameters are explicit and required
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Config:
    name: str
    value: int
    role: str

def save_state(data: bytes, role: str) -> None:
    ...
```

**Why default values are anti-patterns:**
- They hide required information, making bugs silent instead of loud
- They create implicit assumptions that are easy to miss
- They make it easy to forget to pass important parameters
- They violate "explicit is better than implicit"
- They can lead to subtle bugs when the default is wrong for a particular use case

**When default values are acceptable:**
- Only when the user explicitly requests it
- When backward compatibility with existing APIs is required (user must confirm this need)
- Never use default values autonomously

**When custom `__init__` is acceptable:**
- Complex initialization logic that cannot be expressed with `__post_init__`
- Compatibility with existing APIs that require specific signatures
- Performance-critical code where dataclass overhead matters

### Prefer `@cached_property` over `__post_init__`

**Do NOT** use `__post_init__` for derived/computed values. Use `@cached_property` instead:

```python
# ✗ BAD - using __post_init__ for derived values
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Rectangle:
    width: float
    height: float
    area: float = field(init=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "area", self.width * self.height)

# ✓ GOOD - using @cached_property for derived values
from functools import cached_property

@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Rectangle:
    width: float
    height: float

    @cached_property
    def area(self) -> float:
        return self.width * self.height
```

**Why `@cached_property` over `__post_init__`:**
- Lazy evaluation: computed only when accessed, not at construction time
- Clearer semantics: explicitly marks the value as derived, not a true field
- Better separation: keeps computation logic close to the property definition
- Avoids `field(init=False)` boilerplate and the confusion it causes
- More Pythonic: uses standard property pattern instead of dataclass-specific hook

**When `__post_init__` is acceptable:**
- Validation logic that must run at construction time
- Side effects that must occur during initialization (e.g., registering the instance)
- Transforming input values before storing (though consider `field` with converter instead)
- When the computed value is needed for `__hash__` or `__eq__` (with `frozen=True`)

### Prefer `tuple` over `list`

**Do NOT** use `list` unless mutation is required. Use `tuple` by default:

```python
# ✗ BAD - using list for immutable data
def get_colors() -> list[str]:
    return ["red", "green", "blue"]

# ✓ GOOD - using tuple for immutable data
def get_colors() -> tuple[str, ...]:
    return ("red", "green", "blue")
```

**When `list` is acceptable:**
- When you need to mutate the collection (append, extend, pop, etc.)
- When interfacing with APIs that specifically require `list`
- When building collections incrementally where mutation is truly necessary

### Prefer Comprehensions and Generators over `append`

**Do NOT** use `append` in a loop. Use comprehensions or generators instead:

```python
# ✗ BAD - using append in a loop
result = []
for item in items:
    if item.is_valid:
        result.append(item.value)

# ✓ GOOD - using list comprehension
result = [item.value for item in items if item.is_valid]

# ✓ GOOD - using generator expression (lazy evaluation)
result = (item.value for item in items if item.is_valid)

# ✓ GOOD - using tuple comprehension for immutable result
result = tuple(item.value for item in items if item.is_valid)
```

**Why avoid `append`:**
- Comprehensions are more readable and Pythonic
- Generators are memory-efficient for large datasets
- Comprehensions clearly express intent (transform + filter)
- `append` loops hide the pattern and are more verbose

**When `append` is acceptable:**
- Never is acceptable

### Self-Descriptive Variable Names

**Do NOT** use abbreviated variable names. All variable names MUST be self-descriptive and use complete words:

```python
# ✗ BAD - abbreviated variable names
fn = get_handler()
func = create_processor()
cb = on_complete
val = compute_result()
obj = create_instance()
res = fetch_data()
msg = format_output()
cfg = load_settings()
ctx = create_context()
params = get_parameters()
args = parse_arguments()
kwargs = extract_keyword_arguments()

# ✓ GOOD - self-descriptive variable names
handler = get_handler()
processor = create_processor()
on_complete_callback = on_complete
result = compute_result()
instance = create_instance()
response = fetch_data()
message = format_output()
configuration = load_settings()
context = create_context()
parameters = get_parameters()
arguments = parse_arguments()
keyword_arguments = extract_keyword_arguments()
```

**Common forbidden abbreviations:**
- `fn`, `func` → use `function`, `handler`, `callback`, or a domain-specific name
- `cb` → use `callback` or `on_xxx_callback`
- `val` → use `value`, `result`, or a domain-specific name
- `obj` → use `instance`, `object`, or a domain-specific name
- `res` → use `result`, `response`, or a domain-specific name
- `msg` → use `message`
- `cfg`, `conf` → use `configuration`, `config`, or `settings`
- `ctx` → use `context`
- `params` → use `parameters`
- `args` → use `arguments`
- `kwargs` → use `keyword_arguments`
- `idx` → use `index`
- `cnt` → use `count`
- `tmp` → use `temporary` or a more descriptive name
- `ret` → use `result` or `return_value`

**Why self-descriptive names matter:**
- Code is read far more often than it is written
- Abbreviations require mental translation and increase cognitive load
- Self-descriptive names make code self-documenting
- Reduces the need for comments explaining what variables hold
- Makes code review and debugging significantly easier

**When abbreviations are acceptable:**
- Standard loop variables like `i`, `j`, `k` for numeric indices in tight loops
- Well-established domain abbreviations (e.g., `url`, `html`, `json`, `id`)
- Never for function references, callbacks, or domain objects

### Mandatory `super()` with `@override`

**ALL** functions decorated with `@override` **MUST** call `super()`.

- **Never** override a concrete implementation without calling `super()`. Doing so often violates the **Liskov Substitution Principle (LSP)** by breaking the base class's established contract, side effects, or state management.
- **Special Case for `slots=True`**: When using `@dataclass(..., slots=True, ...)`, you **MUST** use the explicit 2-argument form of `super()`: `super(ClassName, self)`. Do **NOT** use the 0-argument `super()` or `super(__class__, self)`, as these can fail due to how Python reconstructs classes with slots.
- If the base class method is an `@abstractmethod` and you do **NOT** want to call `super()`, you **MUST NOT** use `@override`.
- Use `@override` strictly for chain-of-responsibility/extension patterns where you are augmenting base behavior.
- Do **NOT** use `@override` for simple interface implementations of abstract methods where the base implementation is empty or intended to be ignored.

```python
# ✗ BAD - replacing concrete implementation without super() (violates LSP)
class Extended(Base):
    @override
    def process(self):
        # Base.process code is ignored, contract might be broken
        self.new_logic()

# ✗ BAD - using 0-arg super with slots=True
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class MyData(Base):
    @override
    def process(self):
        super().process()  # Might fail with slots=True

# ✓ GOOD - extending concrete implementation with super() (respects LSP)
class Extended(Base):
    @override
    def process(self):
        super().process()
        self.new_logic()

# ✓ GOOD - 2-arg super with literal class name for slots=True
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class MyData(Base):
    @override
    def process(self):
        super(MyData, self).process()
        self.new_logic()

# ✓ GOOD - implementing abstract method WITHOUT @override (no super() needed)
class Concrete(Abstract):
    def do_something(self):
        self.perform_action()
```

**Why this rule exists:**
- **Liskov Substitution Principle (LSP):** Subtypes must be substitutable for their base types. Overriding a concrete method without calling `super()` risks breaking the invariant expectations of the base class.
- **Predictability:** Ensures that method resolution chains are never accidentally broken and that base class logic (initialization, registration, etc.) is always executed.
- **Clarity:** Clearly distinguishes between *implementing* an interface and *extending* existing behavior.

### Representing Optional/Absent Values: Anti-patterns and Correct Pattern

The following are all **anti-patterns** for representing optional or absent values:

```python
# ✗ BAD - Optional[Xxx] or Xxx | None
from typing import Optional

def get_user(id: int) -> Optional[User]:
    return users.get(id)

def get_user(id: int) -> User | None:
    return users.get(id)

# ✗ BAD - Singleton sentinel constants
MISSING = object()
NOT_FOUND = object()
SENTINEL = object()

def get_config(key: str) -> Config | type[SENTINEL]:
    return configs.get(key, SENTINEL)

# ✗ BAD - XxxState enum + Optional[Xxx] in separate fields
class ResourceState(Enum):
    NOT_STARTED = auto()
    RUNNING = auto()
    DESTROYED = auto()

@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Container:
    state: ResourceState
    resource: Resource | None  # Can become inconsistent with state!

# Problem: Two separate fields can become inconsistent
# Even with frozen=True, creating new instances can have mismatched state/resource
```

**Why these are anti-patterns:**
- `Optional[Xxx]` and `Xxx | None` force null checks everywhere, hide design issues
- Singleton sentinels like `MISSING` describe absence, not behavior
- `XxxState` enum + `Optional[Xxx]` in separate fields can become inconsistent
- All violate "explicit is better than implicit"

**The correct pattern: `Xxx | XxxSentinel` (sentinel enum in union)**

```python
# ✓ GOOD - sentinel enum in union consolidates state and resource
class ResourceSentinel(Enum):
    NOT_STARTED = auto()  # Resource hasn't been created yet
    DESTROYED = auto()    # Resource was cleaned up

@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class Container:
    resource: Resource | ResourceSentinel  # Single field, always consistent

# Usage - create instances with the appropriate state
container = Container(resource=ResourceSentinel.NOT_STARTED)  # Before init
container = Container(resource=create_resource())              # After init
container = Container(resource=ResourceSentinel.DESTROYED)    # After cleanup

# Type-safe matching
match container.resource:
    case ResourceSentinel.NOT_STARTED:
        initialize()
    case ResourceSentinel.DESTROYED:
        raise RuntimeError("Resource already destroyed")
    case Resource() as res:
        use(res)
```

**Why `Xxx | XxxSentinel` is good:**
- Single field ensures state and resource are always consistent
- No way to have inconsistent state (e.g., `state=DESTROYED` while `resource` still holds object)
- Type checker enforces exhaustive matching
- Self-documenting: the type annotation tells the full story
- Sentinel enum values describe *behavior* (NOT_STARTED, DESTROYED) not just absence
- Conceptually similar to Java's checked exceptions or Rust's `Result<T, E>`—the sentinel is a typed error channel in the return type that callers must handle

**The most common correct approach: immutable required fields**

In most cases, the simplest way to avoid `Optional` and `| None` is to make fields immutable and required:

```python
# ✓ GOOD - immutable required fields (best design in most cases)
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class User:
    id: int        # Required, never None
    name: str      # Required, never None
    email: str     # Required, never None

# ✓ GOOD - if a field is truly optional, ask: should it be a separate type?
@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class BasicUser:
    id: int
    name: str

@dataclass(kw_only=True, slots=True, frozen=True, weakref_slot=True)
class VerifiedUser:
    id: int
    name: str
    email: str     # Only verified users have email
```

**Other correct approaches:**

```python
# ✓ GOOD - raise exceptions for "not found" cases
def get_user(id: int) -> User:
    if id not in users:
        raise KeyError(f"User {id} not found")
    return users[id]

# ✓ GOOD - behavior enum as return type (not paired with Optional data)
class ValidationResult(Enum):
    VALID = auto()
    INVALID_FORMAT = auto()
    EXPIRED = auto()
    REVOKED = auto()

def validate(token: str) -> ValidationResult:
    ...  # Returns result directly, no Optional pairing

# ✓ GOOD - policy enum controls behavior (not paired with Optional)
class CachePolicy(Enum):
    USE_CACHED = auto()
    FORCE_REFRESH = auto()
    STALE_IF_ERROR = auto()

def fetch(url: str, policy: CachePolicy) -> Response:
    ...  # Policy controls behavior
```

**When `Optional` or `| None` is acceptable:**
- Only when the user explicitly requests it
- Never use it autonomously

