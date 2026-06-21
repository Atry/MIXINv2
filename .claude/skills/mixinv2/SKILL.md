---
name: mixinv2
description: "MIXINv2 language coding conventions: C#-like UpperCamelCase/lowerCamelCase naming with totality semantics, namespace/sort/entity/algebraic-structure/category concepts, the *Factory + Product pattern, abstract factories with declarations, nested-class projection fields, private underscore members, Python FFI module naming (@public/@resource/@extern), and lexical vs qualified-this references. Use when authoring or editing .mixin.yaml files, MIXINv2 Python FFI modules, or anything in the MIXINv2 scope tree."
---

# MIXINv2 Coding Conventions

**Terminology note:** This project previously used the terms "mixin", "union", and "overlay". The language has been renamed to **MIXINv2**. Legacy references to "mixin", "union", or "overlay" in code, comments, or documentation refer to MIXINv2 concepts.

MIXINv2 adopts C#-like naming conventions. The UpperCamelCase/lowerCamelCase distinction is not merely stylistic — it carries semantic meaning for the totality checker: UpperCamelCase symbols are **scopes** (instantiable at runtime), while lowerCamelCase symbols are written as if they are **resources** (lazily evaluated values, no new UpperCamelCase children defined within them). This naming convention enables automatic totality verification without manual proofs (see `mixin_totality.tex`). Note that the scope/resource distinction is a design intent, not yet enforced by the compiler — currently all symbols compile to scopes regardless of casing.

For initialisms/acronyms, follow C#-style casing: keep the acronym uppercase in PascalCase names (for example, `AsyncFFI`, `StdlibFFI`, `HTTPRequest`) rather than mixed forms like `AsyncFfi`.

### Naming Convention Summary

| Element                             | Casing         | Examples                                 | C# Analogy          | Math Analogy                    |
| ----------------------------------- | -------------- | ---------------------------------------- | ------------------- | ------------------------------- |
| namespace                           | UpperCamelCase | `Builtin`                                | namespace           | category / multi-sorted algebra |
| sort (class)                        | UpperCamelCase | `Nat`, `Boolean`, `BinNat`               | class               | sort (carrier set)              |
| algebraic structure (partial class) | UpperCamelCase | `NatPlus`, `BooleanAnd`                  | partial class       | endomorphism (Sort → Sort)      |
| category                            | UpperCamelCase | `NatEquality`, `BinNatEquality`          | —                   | morphism (Sort₁ → Sort₂)        |
| entity                              | UpperCamelCase | `Zero`, `Successor`, `True`, `False`     | —                   | element of a sort               |
| nested class/method                 | UpperCamelCase | `Acceptance`, `Plus`, `Equal`, `And`, `Or`  | method/nested class | —                               |
| field                               | lowerCamelCase | `predecessor`, `addend`, `sum`           | field               | —                               |
| parameter                           | lowerCamelCase | `addend`, `other`, `operand0`            | parameter           | —                               |
| private member                      | `_` prefix     | `_increasedAddend`, `_recursiveAddition` | `private`           | —                               |

### Namespace (UpperCamelCase)

Borrowed from C#. A namespace corresponds to a **category** (or equivalently, a **multi-sorted algebra**). It contains sorts, algebraic structures, and categories as its members.

Example: `Builtin` is a namespace containing sorts (`Nat`, `Boolean`, `BinNat`), algebraic structures (`NatPlus`, `BooleanNegation`), and categories (`NatEquality`, `BinNatEquality`).

### Sort / Entity (UpperCamelCase)

A **sort** (mathematical term) is a carrier set — MIXINv2's equivalent of a C# class. Its data constructors are called **entities** (ECS term). These are two perspectives on the same concept: a sort is defined by its entities, and an entity belongs to a sort.

Sorts are defined using a `*Factory` + `Product` pattern: the factory contains `Product` (the abstract element type) and all entity constructors, while the sort name is aliased to `[*Factory, Product]`:

```yaml
NatFactory:        # Sort factory: natural numbers
  Product: []      # Abstract element type
  Zero:
    - [Product]
  Successor:
    - [Product]
    - predecessor: [Product]
Nat: [NatFactory, Product]   # Sort alias: Nat = NatFactory.Product

BooleanFactory:    # Sort factory: booleans
  Product: []
  "True": [Product]
  "False": [Product]
Boolean: [BooleanFactory, Product]
```

The `*Factory` indirection allows algebraic structures and categories to be composed onto the same factory without modifying the original sort definition. The sort alias (`Nat`, `Boolean`) provides a stable public name.

**Constructing a value** of a sort means inheriting one of its entity constructors and supplying the required fields. This is the constructor design pattern:

```yaml
# To construct a Successor wrapping some value n:
_wrappedN:
  - [Successor]          # inherit the Successor constructor
  - predecessor: [n]     # supply the required field

# To construct an Odd BinNat from an Even half:
_result:
  - [Odd]                # inherit the Odd constructor
  - half: [Even, ~, half]  # supply the required field
```

The result is then exposed via a projection field (e.g. `sum`, `decreased`, `increment`) so callers do not need to know which constructor was used — see Nested Class / Method below.

The entity **name** is its identity — it persists across compositions. Each individual **definition** of that entity within a category is a component. When categories are composed, components with the same entity name merge onto the same entity. For example, `NatData.Zero`, `NatVisitor.Zero`, and `NatPlus.Zero` are three separate components that all merge onto the entity `Zero`:

```yaml
# In NatData.mixin.yaml: Zero is defined as a data variant
NatFactory:
  Product: []
  Zero:
    - [Product]
  Successor:
    - [Product]
    - predecessor: [Product]

# In NatPlus.mixin.yaml: Zero gets a Plus component overlaid
- [NatData]
- NatFactory:
    Zero:
      Plus:
        addend: [Product]
        sum: [addend]   # 0 + m = m

# When composed, the entity Zero has both its original structure
# and the Plus behavior merged together
```

### Algebraic Structure — C# partial class (UpperCamelCase)

Borrowed from C#'s partial class concept. An algebraic structure adds operations to an existing sort, like a partial class adds methods to an existing class. It corresponds to an **endomorphism** (Sort → Sort) in multi-sorted algebra.

```yaml
# NatPlus.mixin.yaml — adds Plus operation to Nat
- [NatData]              # Inherit the sort data definition
- NatFactory:            # Extend the factory
    Product:
      Plus:
        sum: [Product]   # Abstract type declaration
    Zero:
      Plus:
        addend: [Product]
        sum: [addend]    # 0 + m = m
    Successor:
      Plus:
        addend: [Product]
        sum: ...         # S(n) + m = S(n + m)
```

Key points:
- The file itself is a top-level list (no wrapping name like `NatPlus:`) — it is an anonymous category
- Inherits `[NatData]` (the category that defines `NatFactory`), not `[Nat]` (the alias `[NatFactory, Product]`)
- Parameters have type constraints: `addend: [Product]`, not `addend: []`

Examples: `NatPlus` (Nat × Nat → Nat), `BooleanNegation` (Boolean → Boolean, exposes `not` field), `BooleanAnd` (Boolean × Boolean → Boolean), `BooleanOr`, `BooleanEquality`, `BinNatPlus`, `BinNatIncrement`, `NatDecrement`, `BinNatDecrement`.

### Category — cross-sort morphism (UpperCamelCase)

A category encodes operations across different sorts (Sort₁ → Sort₂). Categories are defined as `.mixin.yaml` files that inherit all relevant sort data files and extend the factory:

```yaml
# NatEquality.mixin.yaml — encodes the morphism Nat × Nat → Boolean
- [NatVisitor]       # Inherit Nat visitor infrastructure
- NatFactory:        # Extend the Nat factory with equality
    - Product:
        Equal:
          other: [Product]
          equal: [NatEquality, ~, Boolean]   # Qualified this crosses sort boundary
      Zero:
        Equal:
          other: [Product]
          _OtherAcceptance:
            - [other, Acceptance]
            - VisitorMap:
                ZeroVisitor:
                  equal: [NatEquality, ~, BooleanFactory, "True"]
                SuccessorVisitor:
                  equal: [NatEquality, ~, BooleanFactory, "False"]
              Accepted:
                equal: [NatEquality, ~, Boolean]
          equal: [_OtherAcceptance, Accepted, equal]
      Successor:
        ...
- [BooleanData]      # Inherit Boolean sort data (output sort)
```

Key points:
- The file inherits all required input sort data (`[NatVisitor]`) and output sort data (`[BooleanData]`)
- Operations are defined within the input sort's factory (`NatFactory:`)
- Cross-sort references use qualified this: `[NatEquality, ~, Boolean]` navigates to the Boolean sort within the composed scope

Each `.mixin.yaml` file is a **category** (multi-sorted algebra) that can be composed with other categories — a file may involve multiple sorts and multiple algebraic structures. This is how MIXINv2 natively solves the **expression problem**: composing `NatEquality` with `BooleanNegation` (by inheriting both) automatically gives the returned booleans a `not` field — without modifying either category.

### Abstract Factory Pattern with Declarations

MIXINv2 supports **abstract factories** through declarations. This pattern enables writing polymorphic code that works across multiple concrete factory types.

#### Declaring Abstract Projections (Slots)

A declaration declares an abstract slot with a type constraint, without providing a concrete implementation:

```yaml
# FibonacciFactory declares abstract Zero and One projections
FibonacciFactory:
  Zero: [Product]    # Abstract projection: expects a Product-typed value
  One: [Product]     # Abstract projection: expects a Product-typed value
  Product:
    Fibonacci:
      n: [Product]
      fibonacci: ...  # Uses Zero and One through lexical references
```

**Key insight:** `Zero: [Product]` is **NOT** a reference to a constructor. It is a **type-constrained slot** that concrete factories must satisfy.

#### Creating Abstract Base Classes

To make an abstract factory work with multiple concrete factories, use inheritance:

```yaml
# Step 1: Define abstract base in each concrete factory's data file
# In NatData.mixin.yaml:
NumberFactory: []          # Abstract base factory
NatFactory:
  - [NumberFactory]        # NatFactory inherits from NumberFactory
  - Product: []
    Zero: [Product]
    Successor: [Product]

# In BinNatData.mixin.yaml:
NumberFactory: []          # Same abstract base
BinNatFactory:
  - [NumberFactory]        # BinNatFactory inherits from NumberFactory
  - Product: []
    Zero: [Product]
    Even: [Product]
    Odd: [Product]
```

Now `NumberFactory` is a common base class that both `NatFactory` and `BinNatFactory` inherit from. This enables polymorphic composition.

#### Implementing Polymorphic Operations

Once the abstract base exists, you can write operations that work for **any** factory inheriting from `NumberFactory`:

```yaml
# NumberIsZero.mixin.yaml — works for both Nat and BinNat
- NumberFactory:
    Zero: [Product]        # Declare abstract Zero projection (satisfied by concrete factories)
    Product:
      Equal:
        other: [Product]   # Declare abstract Equal operation (provided by NatEquality/BinNatEquality)
        equal: [NumberIsZero, ~, Boolean]  # equal is inherited from composed categories
      IsZero:
        _equalZero:
          - [Equal]        # Use abstract Equal operation
          - other: [Zero]  # Use abstract Zero projection (lexical reference)
        isZero: [_equalZero, equal]
- [Builtin, BooleanData]
```

**How this works:**
- `NumberFactory.Zero` is a declaration for lexical references within `NumberIsZero.mixin.yaml`
- When composed with `NatFactory`, `[Zero]` resolves to `NatFactory.Zero` (the Nat constructor)
- When composed with `BinNatFactory`, `[Zero]` resolves to `BinNatFactory.Zero` (the BinNat constructor)
- `Equal` is an abstract operation that concrete factories must provide (via NatEquality/BinNatEquality)

#### Pattern Summary

1. **Define abstract base class** in each concrete factory's data file:
   ```yaml
   AbstractFactory: []
   ConcreteFactory:
     - [AbstractFactory]
   ```

2. **Declare abstract projections** with type constraints:
   ```yaml
   AbstractFactory:
     Zero: [Product]   # Abstract projection (slot)
   ```

3. **Implement polymorphic operations** using lexical references to abstract projections:
   ```yaml
   - AbstractFactory:
       Product:
         Operation:
           result: [Zero]  # Lexical reference resolves polymorphically
   ```

4. **Compose with concrete factories** through inheritance:
   ```yaml
   - [Builtin, NumberIsZero]   # Polymorphic operation
   - [Builtin, NatEquality]    # Concrete factory: works with Nat
   ```

### Nested Class / Method (UpperCamelCase)

Prefer **nouns and adjectives** over verbs to reflect MIXINv2's declarative nature:

```yaml
# ✓ GOOD - nouns and adjectives (declarative)
Acceptance:
Accepted:
Plus:
Addition:
Equal:
Negation:
And:
Or:

# ✗ BAD - verbs (imperative)
Add:
Negate:
Compare:
```

A nested class should expose its result as a **projection field** rather than directly inheriting a constructor. Callers read the result through the field; they should not need to know which constructor was used internally:

```yaml
# ✓ GOOD - Plus exposes result via projection field `sum: [Product]`
# Callers use ANF style: bind a temporary variable to Plus, then read sum from it
#   _addition:
#     - [someNat, Plus]
#     - addend: [otherNat]
#   result: [_addition, sum]
Product:
  Plus:
    sum: [Product]    # projection field: abstract result type
Zero:
  Plus:
    addend: [Product]
    sum: [addend]     # Zero + m = m, result is m directly
Successor:
  Plus:
    addend: [Product]
    sum: ...          # S(n) + m = S(n+m), result is a Successor

# ✗ BAD - directly inheriting a constructor leaks implementation details
# Callers would need to know the result is specifically a Successor
Successor:
  Plus:
    - addend: [Product]
    - [Successor]
    - predecessor: ...  # caller must navigate .predecessor, not .sum
```

### Field (lowerCamelCase)

Fields hold values within a class. The compiler currently does not treat fields specially, but they will be compiled to `@resource` in the future — meaning they are lazily evaluated and each value is computed at most once.

```yaml
Successor:
  predecessor: [Product]    # field: lowerCamelCase

Zero:
  Plus:
    addend: [Product]       # parameter: lowerCamelCase
    sum: [addend]           # field: lowerCamelCase
```

### Parameter (lowerCamelCase)

External inputs to operations, declared with a type reference to indicate they must be provided at instantiation time:

```yaml
Plus:
  addend: [Product]     # parameter: must be provided, typed as Product
  sum: [addend]         # field: computed from parameter

Equal:
  other: [Product]      # parameter: must be provided, typed as Product
  equal: [other]        # field: computed from parameter
```

### Private Members (Underscore Prefix)

Underscore prefix denotes private implementation details — intermediate computations not part of the public API.

**Naming rule for private members:** A resource (lowerCamelCase) **can contain** nested scopes via inheritance, but **cannot define** new nested scopes. If a symbol defines new UpperCamelCase children, it must itself be UpperCamelCase — even if private:

```yaml
Successor:
  Equal:
    other: [Product]

    # ✓ GOOD - lowerCamelCase: inherits [Successor] but only provides
    # lowerCamelCase fields (no new scope definitions)
    _increasedAddend:
      - [Successor]
      - predecessor: [addend]

    # ✓ GOOD - UpperCamelCase: defines new nested scopes
    # (VisitorMap, Accepted are new scope definitions)
    _OtherAcceptance:
      - [other, Acceptance]
      - VisitorMap:
            ZeroVisitor:
              equal: [NatEquality, ~, "False"]
            SuccessorVisitor:
              equal: [_recursiveEquality, equal]
          Accepted:
            equal: [NatEquality, ~, Boolean]

    # ✗ BAD - lowerCamelCase but defines new scopes
    _otherAcceptance:
      - [other, Acceptance]
      - VisitorMap:            # Defines a new scope → parent must be UpperCamelCase
            ZeroVisitor:
              equal: ...

    equal: [_OtherAcceptance, Accepted, equal]
```

The distinction: `_increasedAddend` is lowerCamelCase because it only **contains** a Successor scope (via inheritance `- [Successor]`) and provides field values (`predecessor: [addend]`). `_OtherAcceptance` is UpperCamelCase because it **defines** new nested scopes (`VisitorMap`, `Accepted`).

### Python FFI Naming Conventions

Python FFI modules — files that use MIXINv2 decorators (`@public`, `@resource`, `@extern`) — are part of the MIXINv2 scope tree, not ordinary Python code. Their naming must follow **MIXINv2 conventions**, not Python conventions (PEP 8).

**Module file names** are MIXINv2 scope names and use **UpperCamelCase**:

For names that include initialisms/acronyms, use C#-style acronym casing (for example, `FFI`, not `Ffi`).

```
# ✓ GOOD — MIXINv2 scope naming
HttpServerCreate.py
SqliteScalarQuery.py
FormatResponse.py
ExtractUserId.py

# ✗ BAD — Python PEP 8 naming
http_server_create.py
sqlite_scalar_query.py
```

**`@extern` and `@public @resource` function names** are MIXINv2 field/resource names and use **lowerCamelCase** — the same casing as in `.mixin.yaml` files. Do NOT convert to Python snake_case:

```python
# ✓ GOOD — lowerCamelCase, matches .mixin.yaml `handlerClass: []`
@extern
def handlerClass() -> type: ...

# ✓ GOOD — lowerCamelCase, matches .mixin.yaml `serveForever: []`
@public
@resource
def serveForever(server: HTTPServer) -> None:
    server.serve_forever()

# ✗ BAD — snake_case (Python convention, not MIXINv2)
@extern
def handler_class() -> type: ...

# ✗ BAD — UpperCamelCase (scope naming, not resource naming)
@public
@resource
def ServeForever(server: HTTPServer) -> None: ...
```

**`@extern` function parameters** follow the same rule — they are MIXINv2 field names and use lowerCamelCase:

```python
# ✓ GOOD — lowerCamelCase parameters
@public
@resource
def server(host: str, port: int, handlerClass: type) -> HTTPServer:
    return HTTPServer((host, port), handlerClass)

# ✗ BAD — snake_case parameters
@public
@resource
def server(host: str, port: int, handler_class: type) -> HTTPServer:
    return HTTPServer((host, port), handler_class)
```

**Summary:** In Python FFI modules, everything visible to the MIXINv2 scope tree (file names, `@extern` names, `@public @resource` names, parameter names) uses MIXINv2 naming (UpperCamelCase for scopes, lowerCamelCase for fields/resources). Only internal Python helpers (private functions, local variables, type aliases) follow standard Python conventions.

### References: Lexical vs Qualified This

MIXINv2 provides two kinds of references for navigating the scope hierarchy:

#### 1. Lexical Reference `[Symbol]`

A **lexical reference** searches for a symbol in the current lexical scope (the file's static structure).

**Critical constraint:** Lexical references **cannot** access inherited properties (symbols introduced through inheritance).

```yaml
# ✓ GOOD - lexical reference to own property
NumberFactory:
  Zero: [Product]          # Own property: defined in this file
  Product:
    IsZero:
      _equalZero:
        - [Equal]           # Own property: defined in this file
        - other: [Zero]     # Own property: defined in this file
      isZero: [_equalZero, equal]
```

**When lexical references work:**
- Accessing sibling entities or nested scopes defined locally
- Simple, direct lookups within the mixin's own definitions, not inherited ones

#### 2. Qualified This Reference `[ScopeName, ~, path...]`

A **qualified this reference** (essentially "qualified super") navigates through the runtime composition graph to access **inherited properties** — symbols not defined in the current file but available through composition.

**Two key motivations for qualified this:**

1. **Bypass variable shadowing** (lexical scope issue)
2. **Access non-own properties** (properties inherited through composition)

```yaml
# Example: Accessing inherited Boolean from composed BooleanData
- NumberFactory:
    Product:
      Equal:
        equal: [NumberIsZero, ~, Boolean]  # Qualified this: Boolean is inherited, not own
- [Builtin, BooleanData]  # BooleanData provides the Boolean definition
```

**Variable shadowing example (from NatEquality.mixin.yaml):**

```yaml
Equal:
  other:                   # Parameter 'other' in outer scope
    - [Product]
    - predecessor: [Product]
  _recursiveEquality:
    - [Successor, ~, predecessor, Equal]
    - other: [Equal, ~, other, predecessor]  # Defining field 'other'
    #         ^^^^^^^^^^^^^^^^^^
    #         Qualified this to access outer 'other' parameter,
    #         not the 'other:' field being defined here
```

Without qualified this, `[other]` in a lexical reference would be ambiguous:
- Does it refer to the outer `other` parameter?
- Or the `other:` field being defined on this line?

Using `[Equal, ~, other, predecessor]` explicitly navigates from `Equal` scope to the `other` parameter (bypassing the local `other:` being defined), then accesses its `predecessor` field.

**Common patterns:**

```yaml
# Accessing inherited property from composed category
NatFactory:
  Product:
    Equal:
      equal: [NatEquality, ~, Boolean]  # Boolean comes from composed BooleanData
      #       ^^^^^^^^^^^^ scope name in composed result
      #                     ^^^^^^^ inherited property

# Cross-file constructor reference
NatFactory:
  Zero:
    Equal:
      _OtherAcceptance:
        VisitorMap:
          ZeroVisitor:
            equal: [NatEquality, ~, BooleanFactory, "True"]  # BooleanFactory.True is inherited
          #       ^^^^^^^^^^^^ scope name
          #                     ^^^^^^^^^^^^^^^ ^^^^^^ path to inherited entity
```

**When to use qualified this:**
- Accessing properties inherited through composition (non-own properties)
- Bypassing variable shadowing in lexical scope
- Cross-file references where the target is not defined in the current file

**Common mistakes:**

```yaml
# ✗ BAD - using file name instead of factory name
IsZero:
  _equalZero:
    - [Equal]
    - other: [NumberIsZero, ~, Zero]  # WRONG: NumberIsZero is file name, not a factory
    #        ^^^^^^^^^^^^^ File name, not a runtime scope instance

# ✓ GOOD - using lexical reference for own property (simplest)
IsZero:
  _equalZero:
    - [Equal]
    - other: [Zero]  # BEST: lexical reference to own property (defined in this file)

# ✓ GOOD - qualified this for inherited property
IsZero:
  equal: [NumberIsZero, ~, Boolean]  # Boolean is inherited from BooleanData, not own
```

#### Rule: Lexical for Own, Qualified This for Inherited

**Use lexical references `[Symbol]` for own properties (defined in current file).**

**Use qualified this `[Scope, ~, Symbol]` for inherited properties (from composed files).**

Lexical references are simpler but limited to own properties. Qualified this is required when accessing inherited properties or bypassing variable shadowing.

**Important:** Do not use an empty declaration `symbol: []` as a workaround to access inherited properties via lexical reference `[symbol]`. An empty declaration silently creates a new empty scope if the inherited property does not exist (e.g., the base scope was not composed), masking composition mistakes. Qualified this fails with an error in the same situation, providing fail-fast behavior.

```yaml
# ✗ BAD - empty declaration masks missing inherited property
RequestScope:
  - [ffi, HttpSendResponse]
  - written: []                    # Silently creates empty scope if HttpSendResponse is not composed
    response: [written]

# ✓ GOOD - qualified this fails loudly if inherited property is missing
RequestScope:
  - [ffi, HttpSendResponse]
  - response: [RequestScope, ~, written]  # Error if HttpSendResponse does not provide 'written'
```

### Known Limitations

#### .mixin.yaml files cannot be a bare scalar

A `.mixin.yaml` file whose entire content is a single scalar value (string, number, etc.) is **not currently supported**. The top-level structure of a `.mixin.yaml` file must be a mapping (dict) or a list.

```yaml
# ✗ NOT SUPPORTED - entire file is a bare scalar
"Hello World"

# ✗ NOT SUPPORTED - entire file is a bare number
42

# ✓ SUPPORTED - top-level mapping
greeting: "Hello World"
count: 42

# ✓ SUPPORTED - top-level list (anonymous category)
- [SomeInheritance]
- key: value
```

This is a known bug tracked for future fix. When you need to provide a scalar configuration value via `.mixin.yaml`, wrap it in a mapping instead of using a bare scalar file.


