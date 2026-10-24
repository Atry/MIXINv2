# MIXINv2 Specification

## 1. Introduction

MIXINv2 is the successor of [MIXIN](https://github.com/Atry/MIXIN). It is a programming language designed to facilitate the flexible composition and configuration of logic and data structures through the use of _mixins_. Unlike traditional programming languages that use classes or functions as the primary building blocks, MIXINv2 employs a unified concept where everything is represented as a mixin. This approach allows for greater modularity, reusability, and flexibility.

MIXINv2 is a lazily-evaluated, immutable language, meaning that values are only computed when necessary, and once created, they cannot be changed. This design makes MIXINv2 particularly well-suited for applications that require functional purity, such as configuration management, domain-specific language (DSL) creation, and code generation.

MIXINv2 is not limited to a specific platform or target language. It can generate code for multiple languages by representing abstract syntax trees (ASTs) that correspond to various programming languages. This makes MIXINv2 an ideal choice for scenarios involving cross-language interoperability, complex configuration files, and even software synthesis.

### 1.1 Comparison with Other Languages

#### 1.1.1 Object-Oriented Languages

In traditional object-oriented languages like Java or C++, classes and objects are used to encapsulate state and behavior. However, this approach has several limitations that MIXINv2 addresses through its unique design:

- **Complex Inheritance Hierarchies**: Object-oriented languages often require complex class hierarchies to represent different behaviors, leading to rigidity and difficulty in maintenance. Multiple inheritance, in particular, can introduce the "diamond problem," where the same method or property is inherited from multiple sources, causing ambiguity and conflicts.

  - **the MIXINv2 Solution**: MIXINv2 uses a flexible composition model where mixins can be combined and inherited without conflict. Properties are automatically merged, and there is no need for complex inheritance trees. This eliminates the diamond problem and allows for clean, modular inheritance structures.

- **Static and Inflexible Object Models**: Once a class is defined in an object-oriented language, its structure and behavior are fixed. Modifying or extending the behavior often requires creating subclasses or using design patterns like decorators, which can add complexity and reduce clarity.

  - **the MIXINv2 Solution**: Mixins in MIXINv2 can be dynamically composed and configured, allowing for flexible adjustments without altering existing definitions. This dynamic composition model enables developers to easily modify and extend behavior by combining mixins, without the need for static class hierarchies or complex design patterns.

- **Method Overriding and the Risk of Ad Hoc Behavior**: Traditional object-oriented languages rely on method overriding to replace inherited behavior entirely. This can lead to unpredictable behavior, especially in deep inheritance hierarchies, where methods in subclasses may inadvertently shadow those in parent classes, introducing subtle bugs.

  - **the MIXINv2 Solution**: MIXINv2 replaces destructive method overriding with **deep merge**. When multiple parent mixins define the same property, their definitions are merged rather than one replacing another. All inherited properties coexist without conflict. This approach avoids the risks associated with destructive overriding, such as accidental method shadowing or breaking polymorphic behavior, providing a more predictable and safer inheritance model.

- **Overreliance on Design Patterns**: To address limitations in object-oriented design, developers often resort to complex design patterns like Singleton, Factory, and Strategy. While these patterns solve specific problems, they can introduce additional complexity and boilerplate code.

  - **the MIXINv2 Solution**: MIXINv2 can be seen as a metaprogramming language designed to generate code for other languages. Instead of using design patterns to address language limitations, developers can use MIXINv2 to generate consistent and reusable code across multiple languages. By representing abstract syntax trees (ASTs) and configurations as mixins, MIXINv2 allows for the creation of domain-specific languages (DSLs) and the automated generation of language constructs, reducing the need for complex design patterns and enabling more expressive and maintainable code.

Overall, MIXINv2 provides a more modular and flexible alternative to traditional object-oriented languages by using mixin composition instead of class inheritance. Its support for property merging and dynamic composition allows developers to build complex systems more easily and safely. As a metaprogramming language, MIXINv2 excels in generating code for multiple languages, making it a powerful tool for scenarios requiring cross-language interoperability and code generation.

#### 1.1.2 Functional Languages

Functional programming languages like Haskell and Scala emphasize immutability and functional purity, offering benefits such as easier reasoning about code and avoidance of side effects. However, they also come with certain limitations that MIXINv2 addresses through its design:

- **Complexity of Function Composition Syntax**: Functional languages often use advanced and abstract syntax for function composition, such as higher-order functions, monads, and combinators. While powerful, these constructs can be difficult to read and understand, especially for those new to functional programming.

  - **the MIXINv2 Solution**: MIXINv2 employs a more intuitive and declarative approach by representing logic and data structures through mixin composition and configuration. Using familiar data serialization formats like YAML or JSON, MIXINv2 allows developers to define complex behaviors in a hierarchical and readable manner. This reduces the syntactic complexity associated with function composition in traditional functional languages.

- **Complexity of Context Management**: In functional programming, managing context, such as state or environment, often requires explicit passing of context through function parameters or using monads, which can make code verbose and harder to maintain.

  - **the MIXINv2 Solution**: MIXINv2 simplifies context management by allowing mixins to automatically inherit and access properties from their lexical scope. This means that shared context or state can be accessed without the need for explicit parameter passing or complex monadic structures. The unified scoping and inheritance rules in MIXINv2 reduce boilerplate code and make the logic more straightforward.

- **The Expression Problem**: The Expression Problem refers to the difficulty of extending both the set of data types and the set of operations over them in a type-safe and modular way. In functional languages, adding new data types is straightforward, but adding new operations can be challenging without modifying existing code.

  - **the MIXINv2 Solution**: MIXINv2 addresses the Expression Problem by allowing both mixins (representing data types) and properties or methods (representing operations) to be extended and composed modularly. Since mixins can inherit and combine properties from multiple sources without conflicts, developers can add new data types and operations independently. This flexibility enables MIXINv2 to support extensibility in both dimensions, overcoming the limitations faced in traditional functional programming languages.

Overall, MIXINv2 provides a more accessible and flexible alternative to functional programming languages by reducing syntactic complexity, simplifying context management, and addressing the Expression Problem. Its mixin-based composition model allows for the modular and conflict-free extension of both data structures and operations, facilitating the development of complex systems in a more intuitive and maintainable way.

#### 1.1.3 Declarative Configuration Languages

Declarative configuration languages like JSON, YAML, and Nix are widely used to represent static data and configurations. They offer simplicity and readability but often lack the ability to express dynamic logic and complex relationships. MIXINv2 extends these ideas, providing a more powerful and flexible alternative.

- **Static Configuration Limitations**: Traditional configuration languages like JSON and YAML are limited to representing static data structures. They cannot express dynamic relationships or logic, such as conditional values, calculations, or dependencies between configurations.

  - **the MIXINv2 Solution**: MIXINv2 allows for dynamic logic and configuration through mixin composition and inheritance. Properties can be inherited, combined, or overridden based on context, enabling dynamic configurations that adapt to changing conditions. This makes MIXINv2 suitable for scenarios where complex dependencies and conditional configurations are required.

- **Lack of Modularity and Reusability**: In static configuration formats, it is difficult to create modular and reusable components. While YAML supports features like anchors and aliases, these are limited and can lead to complex and error-prone configurations.

  - **the MIXINv2 Solution**: MIXINv2 enables modular and reusable configuration components through its mixin system. Each mixin can encapsulate a piece of configuration or logic, which can then be combined and reused in different contexts. This modular approach not only improves maintainability but also allows for the creation of complex configurations by composing simpler, reusable mixins.

- **Difficulty in Representing Relationships**: Declarative configuration languages often lack the ability to represent complex relationships between different parts of a configuration. Dependencies and relationships must be managed manually, which can lead to errors and inconsistencies.

  - **the MIXINv2 Solution**: MIXINv2 uses inheritance to represent relationships between mixins, enabling clear and maintainable configurations. By using a unified inheritance model, MIXINv2 allows for the automatic resolution of dependencies and relationships, reducing the risk of errors and inconsistencies.

- **Limited Expressiveness for Code Generation**: While declarative languages like Nix provide some level of code generation through lazy evaluation and functional constructs, they are primarily designed for configuration management and package management. Extending them for general-purpose code generation or complex logical expressions can be cumbersome.

  - **the MIXINv2 Solution**: MIXINv2, as a metaprogramming language, is designed to generate code and configurations for multiple target languages. By representing abstract syntax trees (ASTs) and logical structures as mixins, MIXINv2 can be used to generate code in different languages consistently. This capability makes MIXINv2 ideal for building DSLs, automating code generation, and ensuring consistency across different language environments.

Overall, MIXINv2 extends the capabilities of traditional declarative configuration languages by supporting dynamic logic, modularity, and complex relationships. Its mixin-based approach enables more expressive and maintainable configurations, and its metaprogramming capabilities make it a powerful tool for code generation and cross-language interoperability.

### 1.2 Key Use Cases

#### 1.2.1 Multi-language Code Generation

MIXINv2 can generate code in multiple target languages, making it a versatile tool for building DSLs or serving as the core module of a compiler. By representing the ASTs of various languages as mixins, MIXINv2 can translate a single logical structure into multiple programming languages, ensuring consistency and reducing duplication across projects.

#### 1.2.2 Cross-language Interoperability

MIXINv2 provides a unified way to define data structures and logic that can be shared across different programming environments. For instance, a complex business logic model defined in MIXINv2 can be translated into both a backend service in Scala and a frontend component in JavaScript, ensuring consistent behavior and data flow.

#### 1.2.3 Complex System Configuration

As a configuration language, MIXINv2 excels in defining complex systems with interdependent components. Through the use of mixin composition and inheritance, configuration files can be modular, reusable, and adaptable, enabling powerful and flexible system configurations that go beyond the capabilities of traditional static formats like JSON or YAML.

### 1.3 A Simple Example

The following example demonstrates how to use MIXINv2 to define a basic arithmetic operation represented as an AST:

```yaml
# math_operations.mixin.yaml

Number:
  - {} # A mixin that represents a number type.

add:
  - [Number] # Inherits from the 'Number' mixin.
  - addend1: [Number] # Property 'addend1', which is a 'Number'.
  - addend2: [Number] # Property 'addend2', which is also a 'Number'.

multiply:
  - [Number] # Inherits from the 'Number' mixin.
  - multiplicand: [Number] # Property 'multiplicand', which is a 'Number'.
  - multiplier: [Number] # Property 'multiplier', which is also a 'Number'.
```

```yaml
# test.mixin.yaml

example_calculation:
  - [add]
  - addend1:
      - [multiply]
      - multiplicand: 2
      - multiplier: 3
  - addend2: 4
```

**Explanation**:

1. The `Number` mixin represents a basic number type with no initial value, aligning with MIXINv2's immutable and lazy-evaluated nature.
2. The `add` mixin inherits from `Number` and defines two properties, `addend1` and `addend2`, both of which are also `Number`.
3. The `multiply` mixin defines a multiplication operation with two properties: `multiplicand` and `multiplier`.
4. In `test.mixin.yaml`, the `example_calculation` mixin uses the `add` operation to add two numbers:
   - `addend1` is a multiplication of `2` and `3`, represented using the `multiply` mixin.
   - `addend2` is the constant `4`.

This example illustrates how MIXINv2 can be used to represent complex logic in a modular and declarative manner. The `example_calculation` mixin serves as the root of an AST, with each operation (e.g., `add` and `multiply`) acting as nodes, and their properties (`addend1`, `addend2`, `multiplicand`, `multiplier`) as sub-nodes. This structure can be evaluated directly within MIXINv2 or used to generate equivalent code in another language.

## 2. Mixin Definitions and Data Types

### 2.1 Basic Structure and Data Types

MIXINv2 supports a range of data types, all of which map directly to JSON data types. These types form the foundational elements of the language and define how data is represented and manipulated within MIXINv2.

#### 2.1.1 Primitive Data Types

The primitive data types in MIXINv2 correspond directly to JSON's scalar types:

- **Strings**: Represented as sequences of characters, corresponding to JSON strings.

  - Example: `"hello, world"`

- **Numbers**: Can be either integers or floating-point numbers, just like JSON numbers.

  - Example: `42`, `3.14`

- **Booleans**: Represent truth values, with `true` and `false` as the only valid values.

  - Example: `true`, `false`

- **Null**: Represents the absence of a value, similar to JSON `null`.
  - Example: `null`

#### 2.1.2 Mixins as Data Types

In MIXINv2, the primary data type is the mixin itself, which corresponds to JSON objects. Each mixin represents a collection of properties and can inherit from other mixins, enabling complex compositions and configurations.

- **Mixin**: Corresponds to a JSON object, with each key representing a property name and each value representing a mixin, primitive type, or an inheritance to another mixin.

  Example:

  ```yaml
  Number:
    - {} # A mixin with no properties, representing a number type.

  add:
    - [Number] # Inherits from the 'Number' mixin.
    - addend1: [Number] # Property 'addend1', which is a 'Number'.
    - addend2: [Number] # Property 'addend2', which is also a 'Number'.
  ```

  In this example:

  - The `Number` mixin serves as a base mixin with no initial properties.
  - The `add` mixin inherits from `Number` and introduces two new properties, `addend1` and `addend2`, both of which are of type `Number`.

#### 2.1.3 Relationship to JSON

MIXINv2's data types map directly to JSON types:

- **JSON Object → Mixin**: A mixin is defined by a JSON object where keys are property names, and values can be mixins or primitive data types.
- **JSON Scalar Types → Primitive Data Types**: JSON strings, numbers, booleans, and null values map directly to MIXINv2's corresponding primitive data types.

#### 2.1.4 No First-class List Support

Unlike JSON, MIXINv2 does not support lists as a first-class type within the language itself. This means that you cannot directly define or manipulate lists in the core MIXINv2 as you would in JSON. Instead, lists are defined and manipulated through MIXINv2 standard library. This design choice maintains the simplicity and consistency of the language by focusing on mixin composition and inheritance. For scenarios requiring list-like structures or operations, MIXINv2 encourages using custom mixins to represent collections or sequences of data.

### 2.2 Properties

Properties are the fundamental components of a mixin, defining its internal state or behavior. The value of a property can be one of the following types:

1. **Basic Data Types**: Strings, numbers, booleans, or null.
2. **Inheritance**: Properties can inherit other mixins by specifying their path, allowing for inheritance and reuse of existing mixins.

#### Property Definition Syntax

The definition of a property resembles key-value pairs in JSON or YAML. Unlike most programming languages, property names in MIXINv2 do not need to be unique. If the same property name is defined multiple times, all definitions will always be automatically merged through multiple inheritance. This allows for the creation of complex and modular structures without conflict.

Example:

```yaml
Person:
  - name: [String] # Defines a 'name' property of type String
  - age: [Number] # Defines an 'age' property of type Number
  - is_married: [Boolean] # Defines an 'is_married' property of type Boolean
```

In this example, if `name` is defined again in a different mixin and both mixins are inherited, the resulting mixin will contain all definitions of `name`.

#### Nested Properties

Property values can be nested mixins, creating more complex structures. For example, we can define an `Address` property within the `Person` mixin:

```yaml
Address:
  - street: [String] # Defines a 'street' property
  - city: [String] # Defines a 'city' property
  - zip_code: [String] # Defines a 'zip_code' property

person_with_address:
  - [Person] # Inherits the 'Person' mixin
  - address: [Address] # Adds an 'address' property using the 'Address' mixin
```

In this example, the `person_with_address` mixin inherits from `Person` and includes a nested `address` property that inherits the `Address` mixin.

### 2.3 Inheritance

In MIXINv2, inheritance is the mechanism by which a mixin inherits all properties and scalar values from another mixin. A mixin selects what to inherit from with a **reference**: an array of strings that indicates the path to the target mixin. (The core inheritance-calculus reserves the word _inheritance_ for the deep merge that a reference triggers, and calls the array itself a _reference_; this specification follows that distinction.)

#### Grouping Property Definitions in Lists

When defining a mixin, you can optionally put properties in lists (i.e., using the `-` symbol in YAML) to indicate the hierarchical structure of properties. When a mixin inherits from other mixins, properties must be prefixed with `-` to avoid confusion between inheritance chains and property declarations. This prefix is optional when there is no inheritance.

**Why Use the `-` Prefix for Properties**

In YAML, a node must be either an array or an object; it cannot contain both array elements and object members simultaneously. Therefore, when a mixin inherits other mixins, the `-` prefix is required to clearly indicate that each property is an item in an array. This prefix is optional when there is no inheritance but is mandatory when inheritance is involved.

**Invalid YAML**:

```yaml
my_car:
  - [Vehicle]          # Inherits the 'Vehicle' mixin
  color: [String]    # Adds a new property 'color'
  doors: [Number]    # Adds a new property 'doors'
```

In the example above, the `my_car` node simultaneously contains an array element (`[Vehicle]`) and object members (`color` and `doors`), which violates the structural rules of YAML.

**Valid YAML**:

```yaml
my_car:
  - [Vehicle] # Inherits the 'Vehicle' mixin
  - color: [String] # Adds a new property 'color'
  - doors: [Number] # Adds a new property 'doors'
```

In this valid example, each element within the `my_car` node begins with the `-` prefix, indicating that these properties are part of an array. This allows the YAML parser to correctly interpret the structure of `my_car`.

#### Multiple Inheritance and Scalar Values

MIXINv2 supports conflict-free multiple inheritance and allows scalar values to be inherited from multiple sources. This means a mixin can combine properties and scalar values from multiple parent mixins without any conflict. All inherited properties and values are integrated seamlessly, resulting in a unified set of properties for the inheriting mixin.

**Example of Multiple Inheritance with Scalar Values**

MIXINv2 allows scalar values to coexist and be inherited along with other properties, as shown below:

```yaml
Number:
  - {} # Defines an empty number type mixin

my_number:
  - 42 # Defines the scalar value 42
  - [Number] # Inherits the 'Number' mixin
```

In this example, `my_number` has both a scalar value `42` and inherits the `Number` type mixin, demonstrating that scalar values and type mixins can coexist and be inherited together.

**Conflict-Free Inheritance**

In MIXINv2, properties with the same name defined in multiple parent mixins are always automatically merged:

```yaml
# basic_features.mixin.yaml
Vehicle:
  - wheels: [Number]
  - engine: {}

Motor:
  - engine:
      gasoline: true # Defines a default scalar value for 'engine'

# advanced_features.mixin.yaml
hybrid_car:
  - ["basic_features", Vehicle]
  - ["basic_features", Motor]
  - wheels: 4 # Defines the scalar value for 'wheels'
  - engine:
      hybrid: true # Defines the scalar value for 'engine'
  - battery_capacity: 100 # Adds a new 'battery_capacity' property
```

In this example, `hybrid_car` inherits the `engine` property from both `Vehicle` and `Motor`. Instead of a conflict, the properties are merged, along with its extra property `hybrid`, which `hybrid_car` explicitly defines. The `battery_capacity` property is added uniquely to `hybrid_car`.

## 3. Syntax and Grammar

### 3.1 Lexical Structure

MIXINv2 is a language that leverages the lexical structures of JSON, YAML, and TOML, focusing on their ability to represent structured data in a clear and readable manner. This section outlines the core syntax and grammar of MIXINv2, emphasizing its usage of these formats and how they correspond to MIXINv2's data and logic constructs.

MIXINv2 does not have its own unique lexical structure; instead, it directly adopts the lexical structures of JSON, YAML, and TOML. This means that any syntax that can be converted into JSON is valid in MIXINv2. Specifically:

- **JSON**: Fully supported, including all standard JSON types and structures.

- **YAML**: Supported as long as it can be losslessly converted into JSON. This means that only a subset of YAML is used, excluding features such as:

  - **Anchors and Aliases**: YAML constructs like `&` (anchor) and `*` (alias) are not supported as they cannot be directly represented in JSON.
  - **Tags**: YAML's type tags (e.g., `!!str`, `!!int`) are not supported, as MIXINv2 uses its own data type system.
  - **Complex Data Types**: Data types like sets, timestamps, and ordered mappings are not supported.

- **TOML**: Supported in its JSON-compatible subset, which includes basic data types like strings, finite numbers, booleans, and dates, but excludes date/time datatypes.

By utilizing these existing formats, MIXINv2 ensures a seamless integration with widely-used data serialization standards, making it easy to define complex data structures and configurations.

#### 3.1.1 Examples of Supported and Unsupported Syntax

**Supported JSON Syntax**:

```json
{
  "name": "example",
  "value": 42,
  "is_active": true,
  "data": null
}
```

**Supported YAML Syntax**:

```yaml
name: example
value: 42
is_active: true
data: null
```

**Unsupported YAML Syntax** (anchors and aliases):

```yaml
base: &base_value
  name: example

derived:
  <<: *base_value
  value: 42
```

**Supported TOML Syntax**:

```toml
name = "example"
value = 42
is_active = true
```

**Unsupported TOML Syntax** (time):

```toml
data = 23:22:21.0123
```

## 4. File Structure and Formats

### 4.1 Supported File Formats

MIXINv2 supports the following file formats for representing source code:

- **YAML**: File extension `.mixin.yaml` (or `.mixin.yml`). Legacy: `.oyaml`, `.oyml`.
- **JSON**: File extension `.mixin.json`. Legacy: `.ojson`.
- **TOML**: File extension `.mixin.toml`. Legacy: `.otoml`.

MIXINv2 uses these formats to define mixins in a structured and human-readable manner. The formats share the following characteristics:

1. **JSON Compatibility**: All supported formats must be serializable to JSON. This means that only the subset of YAML and TOML that can be converted to JSON without loss of information is supported.

2. **File Extensions**: The file extension must indicate the format and its use as a MIXINv2 file: `.mixin.yaml`, `.mixin.json`, or `.mixin.toml` (legacy: `.oyaml`, `.ojson`, `.otoml`).

3. **Lossless Conversion**: The language only uses features that can be converted between the supported formats without loss of information.

### 4.2 File and Mixin Naming Conventions

#### 4.2.1 File Naming Conventions

- **Format**: Use lowercase letters with underscores to separate words. File names must use the `.mixin` prefix before the format extension (e.g., `.mixin.yaml`, `.mixin.json`, `.mixin.toml`) to indicate they are MIXINv2 files. Legacy extensions `.oyaml`, `.ojson`, `.otoml` are also supported.

- **Type Definition**: Use singular nouns if defining a primary concept (e.g., `vehicle.mixin.yaml`). Use plural nouns if the file contains multiple instances or variations (e.g., `vehicles.mixin.yaml`).

**Examples**:

- `vehicle.mixin.yaml`
- `vehicles.mixin.yaml`
- `test_cases.mixin.json`

#### 4.2.2 Mixin Naming Conventions

Mixin names within files must follow these conventions based on their intended use:

1. **Type-like Mixins**:

   - Use UpperCamelCase naming (e.g., `PersonDetails`, `Vehicle`). These mixins represent types and can be inherited by other mixins.
   - Should not include scalar values; instead, focus on defining structured data or behaviors.

2. **Value-like Mixins**:

   - Use lowercase with underscores (e.g., `height_value`, `name`). These mixins typically represent individual values or instances and may include scalar values.

3. **Instance Mixins**:

   - Use lowercase with underscores (e.g., `electric_vehicle`, `combined_person`) to represent specific instances or configurations and may inherit from multiple type-like mixins.

### 4.3 Cross-File Inheritance

MIXINv2 allows inheriting mixins defined in different files. The rules for cross-file inheritance are as follows:

1. **Inheritance Format**:

   - A reference is represented as an array of strings, where each string corresponds to a segment in the path to the target mixin.
   - The format for a cross-file reference is `[path, to, mixin_name]`, where `path` is the relative path from the current file to the target mixin, excluding the top-level directory name.

2. **Directory Scope**:

   - Each directory has its own lexical scope. Files within the same directory can inherit each other using just the file name and mixin name (e.g., `[file_name, mixin_name]`).
   - Directories do not share scopes, meaning that a mixin defined in one directory cannot directly inherit a sibling directory's mixin without specifying the correct path.

3. **Lexical Scope Resolution**:

   - MIXINv2 automatically searches for inheritances starting in the current directory. If not found, it searches in the parent directory, and then the parent's parent directory, continuing upwards until the root is reached.
   - The first segment of the inheritance looks for the mixin name in the current lexical scope, which includes:

     - **Current File**: Mixins defined in the same file.
     - **Parent Mixins**: Mixins in the parent scope of the current mixin.
     - **Directory Scope**: Mixins defined directly in the current directory.

   - Subsequent segments can access properties in the inherited mixin hierarchy if the first segment resolves to a mixin in the scope.

4. **Isolated File Scopes**:

   - Mixins defined in separate files within the same directory do not share lexical scopes with each other. They can only access mixins from the directory scope and their own file.

5. **No `..` Syntax for Parent Directory**:

   - MIXINv2 does not support the `..` syntax to navigate to parent directories. Instead, the language automatically searches upward through the directory structure, starting from the current directory.

#### 4.3.1 Example of Cross-File Inheritance

**Directory Structure**:

```
project/
│
├── module/
│   ├── vehicle.mixin.yaml
│   ├── electric.mixin.yaml
│   └── car.mixin.yaml
│
├── config/
│   └── settings.mixin.yaml
└── test/
    └── test_car.mixin.yaml
```

**vehicle.mixin.yaml**:

```yaml
Vehicle:
  engine: {}
  wheels: [Number]
```

**electric.mixin.yaml**:

```yaml
Electric:
  - engine:
      electric: true
  - battery_capacity: [Number]
```

**car.mixin.yaml**:

```yaml
Car:
  - [Vehicle]
  - [Electric]
  - model: [String]
```

**test_car.mixin.yaml**:

```yaml
test_car:
  - [module, Car] # Cross-directory inheritance to Car in module/car.mixin.yaml
  - model: "Test Model"
  - test_battery:
      - [module, Electric, battery_capacity] # Inheritance to battery_capacity in Electric
```

In this example:

- The `test_car` mixin in `test_car.mixin.yaml` inherits `Car` and `Electric` from the `module` directory using the format `[module, Car]` and `[module, Electric, battery_capacity]`.
- The first segment of the inheritance (`module`) indicates the directory in which the target mixins are located.
- The inheritance format and scope rules ensure that mixins are correctly resolved based on the file and directory structure.


## 5. Scope and Inheritance Resolution

### 5.1 Scope Definition

In MIXINv2, scope determines the visibility and inheritance relationships of mixins and properties within the current context. The scope structure includes sibling mixins, parent mixins, directory scope, and cross-file inheritance.

**Scope in MIXINv2 consists of the following levels**:

- **Sibling Mixins**: The names of other mixins in the same file are visible in the current scope and can be inherited using the format `[mixin_name]`. Inheritance from sibling mixins takes precedence over parent mixin inheritance.

- **Parent Mixins**: The names of all parent mixins in the current hierarchy are visible in the current scope. Resolution starts from the parent scope (not the mixin itself), so a mixin's own name is not directly in its own lookup scope. Additionally, **same-name skip semantics** apply: when a mixin references a name that matches its own key, the first match found during the upward traversal is skipped. This allows a mixin to reference an outer mixin with the same name without creating a self-reference. For example, if `Inner.value` references `[value]`, the algorithm skips the first `value` it finds (which would be `Inner.value` seen from its parent) and resolves to an outer `value` instead. See Section 5.2.1 for the full resolution algorithm.

- **Directory Scope**: A directory has a lexical scope that includes all mixins defined directly within that directory. Files within the directory can inherit mixins in the directory's scope using the format `[directory_name, mixin_name]`.

- **Cross-File Inheritance**: When inheriting mixins across different directories, the path must include the relative path from the current file to the target mixin.

MIXINv2 does not distinguish between types and values. Any mixin can represent either a data value or a type. However, in practice, type-like mixins are usually named using the UpperCamelCase convention and represent structures or behaviors to be inherited. Value-like mixins are named using lowercase letters with underscores and typically represent individual values or instances.

### 5.2 Reference Resolution

References in MIXINv2 are resolved **dynamically at the time of mixin evaluation or inheritance**. How the first segment of a reference finds its scope determines what the reference resolves to.

#### 5.2.1 First Segment Resolution

A **lexical reference** (an all-string array) climbs outward through the enclosing scopes until it finds the nearest scope that _defines_ its first segment, then projects the remaining segments downward from there. Reading the segments left to right is projection, with the comma playing the role of the `.` in other languages.

- **First Segment Resolves to an Outer Mixin**: If the first segment names an outer mixin (e.g., `[Outer, sibling]`), the reference reads as `Outer.sibling`: it resolves `Outer` in an enclosing scope and then projects `sibling`. This is useful when you want to reach a mixin defined in an enclosing scope. To reach the dynamic `self` of that enclosing scope rather than a lexically defined one, use the qualified this syntax `[Outer, ~, sibling]` instead (see Section 5.2.4).

- **First Segment Resolves to a Sibling Mixin**: If the first segment names a sibling mixin (e.g., `[sibling, sibling_property]`), the reference reads as `sibling.sibling_property`: it resolves the `sibling` mixin in the current context and then projects `sibling_property`. This lets you reach mixins defined alongside the current mixin.

- **First Segment Resolution in Lexical Scope**:

  - The first segment of the reference searches for the mixin name in the current lexical scope, which includes:

    - **Current File**: Mixins defined within the same file.

    - **Parent Mixins**: Mixins in the parent scope of the current mixin.

    - **Directory Scope**: Mixins defined directly within the current directory.

  - **No Inheritance Lookup in First Segment**: The first segment does not search for properties within inherited mixins. To reference inherited members, use qualified this syntax: `[ScopeName, ~, inherited_member]`.

- **Same-Name Skip Semantics**:

  Lexical references implement **same-name skip semantics** (analogous to pytest fixture shadowing). When the first segment of a reference path matches the defining mixin's own key, the first match encountered during the upward scope traversal is skipped, and resolution continues to the next outer scope.

  **Algorithm**:

  1. Let `first_segment` be the first element of the reference path.
  2. If `first_segment` equals the current mixin's key, set `skip_first = true`.
  3. Starting from the parent scope (not the mixin itself), traverse upward through enclosing scopes:
     a. At each scope, check if `first_segment` is an **own property** (not inherited) of that scope.
     b. If found and `skip_first` is `true`: set `skip_first = false` and continue to the next outer scope.
     c. If found and `skip_first` is `false`: resolve the reference to this scope.
     d. If not found: continue to the next outer scope.
  4. If the root is reached without a match, raise a lookup error.

  **Example — single level**:

  ```yaml
  Root:
    value: 10
    Inner:
      value:
        - [value]    # References Root.value (10), not Inner.value itself
        - # ... computes value + 1, resulting in 11
  ```

  Here, `Inner.value` references `[value]`. Because `first_segment` (`value`) matches `Inner`'s own key (`value`), the algorithm skips the first match (the `value` property found in `Root` that corresponds to `Inner.value`'s sibling) and resolves to `Root.value` instead.

  **Example — multiple levels**:

  ```yaml
  Root:
    value: 10
    Level1:
      value:
        - [value]    # Skips Level1.value, resolves to Root.value (10) → 11
      Level2:
        value:
          - [value]  # Skips Level2.value, resolves to Level1.value (11) → 12
  ```

  At each nesting level, the same-name skip ensures that `[value]` resolves to the nearest outer `value`, not to the mixin being defined. This enables recursive-like compositional patterns where each level wraps the value from the level above.

#### 5.2.2 Subsequent Segment Resolution

After resolving the first segment, subsequent segments can access properties within the inherited mixin hierarchy.

- **Inherited Properties**: Subsequent segments can access properties inherited from parent mixins.

- **Dynamic Resolution**: Inheritances are resolved dynamically, meaning that if inherited mixins are extended or overridden in the current context, the inheritance reflects these changes.

#### 5.2.3 Reference Resolution Example

Consider the following example:

```yaml
OuterMixin:
  inner_mixin:
    property: "value"

CurrentMixin:
  - [OuterMixin]
  - inheriting_inner:
      - [OuterMixin, inner_mixin]  # Lexical reference resolving to an outer mixin
  - inheriting_sibling:
      - [sibling_mixin, property]  # Lexical reference resolving to a sibling mixin
  sibling_mixin:
    property: "sibling value"
```

Both `inheriting_inner` and `inheriting_sibling` use lexical references (all-string arrays), differing only in where their first segment resolves:

- **`inheriting_inner`** references `[OuterMixin, inner_mixin]`:

  - **First Segment**: `OuterMixin`, resolved as an outer mixin in an enclosing scope.

  - **Resolution**: The reference reads as `OuterMixin.inner_mixin`, inheriting the `inner_mixin` defined under `OuterMixin`.

- **`inheriting_sibling`** references `[sibling_mixin, property]`:

  - **First Segment**: `sibling_mixin`, resolved as a sibling mixin defined in the same file.

  - **Resolution**: The reference reads as `sibling_mixin.property`, inheriting the `property` defined under `sibling_mixin`.

#### 5.2.4 Qualified This Syntax

When a reference needs to access the dynamic `self` of an enclosing mixin (analogous to `Outer.this` in Java), MIXINv2 provides an explicit **qualified this** syntax:

```yaml
- [OuterMixin, ~, property, path]
```

This is an array where the first element is a string (the `selfName` of an enclosing scope), the second element is `null` (written as `~` in YAML), and the remaining elements are strings (the path to navigate within that scope's dynamic `self`). This is analogous to Java's `Outer.this.property.path`.

**Semantics**: The evaluator walks the symbol table chain to find a scope whose `selfName` matches the first element, retrieves that scope's dynamic `self` (the fully composed evaluation), and then navigates the path segments through `allProperties`.

**Example**:

```yaml
NatAdd:
  - [types, Nat]                    # Inheritance (all-string array)
  - augend:
      - [types, Nat]
    addend:
      - [types, Nat]
    _applied_addend:
      - [NatAdd, ~, addend]         # Qualified this: NatAdd.self.addend
      - successor:
          - [NatAdd, ~, successor]  # Qualified this: NatAdd.self.successor
        zero:
          - [NatAdd, ~, zero]       # Qualified this: NatAdd.self.zero
    result:
      - [_applied_addend, result]   # Regular variable reference (not qualified this)
```

In this example, `[NatAdd, ~, successor]` accesses `successor` through NatAdd's dynamic `self`. This is necessary because `successor` is inherited from `Nat` and not directly accessible as a lexical variable within `_applied_addend`'s scope (where `successor` is shadowed by `_applied_addend`'s own property).

**When to use qualified this vs. direct references**:

- Use a direct reference `[property]` or `[property, subproperty]` when the first segment is accessible in the current lexical scope (as an own property or via outer scopes).
- Use qualified this `[SelfName, ~, property, path]` when the property is only accessible through the dynamic `self` of an enclosing mixin (e.g., inherited properties that are shadowed in the current scope).

**Distinction from lexical references**: A lexical reference is an all-string array like `[types, Nat]`. A qualified this reference contains a `null` delimiter after the self name: `[NatAdd, ~, successor]`. The evaluator distinguishes between these based on whether the second element is `null`.

#### 5.2.5 Cross-Directory Inheritance

When inheriting mixins across different directories, the path must include relative path segments:

```yaml
- [path, to, mixin_name, property]
```

- **First Segment**: `path` is interpreted relative to the directory structure of the current file.

- **Resolution**: MIXINv2 will automatically search for the inherited mixin by traversing the directory hierarchy.

### 5.3 Multiple Inheritance and Scalar Value Handling

MIXINv2 supports **conflict-free multiple inheritance**, allowing mixins to inherit properties and scalar values from multiple parent mixins without conflicts. This feature enables the flexible composition of complex structures by combining the functionalities of various mixins.

#### 5.3.1 Inheritance and Property Merging

When a mixin inherits from multiple parent mixins, the properties from all parents are **merged** into the inheriting mixin. If multiple parent mixins define the same property, the definitions are automatically combined, avoiding naming conflicts and preserving all inherited behaviors.

**Example:**

```yaml
# basic_features.mixin.yaml
Vehicle:
  - wheels: [Number]
  - engine: {}

Motor:
  - engine:
      gasoline: true # Scalar value for 'engine'

# advanced_features.mixin.yaml
hybrid_car:
  - ["basic_features", Vehicle]
  - ["basic_features", Motor]
  - wheels: 4 # Scalar value for 'wheels'
  - engine: # Merging with 'Vehicle.engine'
      hybrid: true
  - battery_capacity: 100 # New property
```

In this example:

- **Inheritance**:
  - `hybrid_car` inherits from both `Vehicle` and `Motor`.
- **Property Merging**:
  - The `engine` property is defined in both parent mixins.
  - MIXINv2 automatically merges the `engine` property without conflict.
- **Resulting Properties**:
  - `hybrid_car` has access to all properties from both parents: `wheels`, `engine`, and `battery_capacity`.

#### 5.3.2 Scalar Value Merging

Scalar values (e.g., strings, numbers, booleans) can coexist with properties within a mixin and can be inherited from multiple parent mixins. MIXINv2 does not define specific rules for merging scalar values from different parents; instead, scalar values from all parents are included in the inheriting mixin without causing errors. The **specific merging behavior** of scalar values is defined by the libraries used in conjunction with MIXINv2, allowing for different strategies depending on the application's needs.

**Example:**

```yaml
# number.mixin.yaml
Number:
  - {} # Represents a number type mixin

# value.mixin.yaml
value_42:
  - 42 # Defines scalar value 42

# my_number.mixin.yaml
my_number:
  - [Number]
  - [value_42]
```

In this example:

- **Inheritance**:
  - `my_number` inherits from both `Number` and `value_42`.
- **Scalar Value Coexistence**:
  - Combines the scalar value `42` and any properties from `Number`.
- **No Conflict**:
  - Scalar values and properties coexist without conflict in `my_number`.

#### 5.3.3 Merging Scalar Values with Properties

A mixin can have both scalar values and properties, and these can be inherited from multiple parents. MIXINv2 allows this combination without conflicts, enabling more expressive and flexible mixin definitions.

**Example:**

```yaml
# person.mixin.yaml
PersonDetails:
  name: [String]
  age: [Number]

# height.mixin.yaml
height_value: 180 # Scalar value representing height

# combined_person.mixin.yaml
combined_person:
  - [PersonDetails]
  - name: "John Doe"
  - age: 30
  - [height_value]
```

In this example:

- **Inheritance**:
  - `combined_person` inherits from both `PersonDetails` and `height_value`.
- **Combined Properties and Scalar Values**:
  - Includes properties `name` and `age`, and scalar value `180`.
- **No Conflict**:
  - Both properties and scalar values are accessible without conflict.

#### 5.3.4 Conflict-Free Inheritance

MIXINv2's approach to inheritance ensures that properties and scalar values from multiple parents are merged seamlessly. This conflict-free inheritance model eliminates issues commonly associated with multiple inheritance in other languages, such as the diamond problem.

- **Automatic Merging**: Properties with the same name are automatically merged.
- **No Overwriting**: Scalar values and properties from different parents do not overwrite each other unless explicitly redefined in the inheriting mixin.
- **Flexibility**: Developers can compose mixins freely without worrying about inheritance conflicts.

**Example of Conflict-Free Inheritance:**

```yaml
# basic_features.mixin.yaml
Vehicle:
  - wheels: [Number]
  - engine:
      gasoline: true # Scalar value for 'engine'

Motor:
  - engine: {} # Defines 'engine' property

# advanced_features.mixin.yaml
hybrid_car:
  - ["basic_features", Vehicle]
  - ["basic_features", Motor]
  - wheels: 4 # Scalar value for 'wheels'
  - engine: # Merging with 'Vehicle.engine'
      hybrid: true
  - battery_capacity: 100 # New property
```

In this example:

- **Inheritance**:
  - `hybrid_car` inherits from both `Vehicle` and `Motor`.
- **Property Merging**:
  - Merges `engine` properties from parents.
- **Resulting Properties**:
  - Combines properties `wheels`, `engine`, and `battery_capacity` in `hybrid_car`.

## 6. Reference Forms and What They Resolve To

References in MIXINv2 resolve dynamically against the fully inherited mixin tree. What a reference resolves to therefore depends on **which enclosing scope its first segment names**, not on any binding time. A qualified this that names an outer, absolute scope reaches a fixed target; a qualified this that names a reusable scope, or a lexical reference, reaches a target that adapts to the current context. The following example illustrates all three.

### 6.1 Example

Consider the following MIXINv2 definition:

```yaml
test_binding:
  my_mixin1:
    - inner:
        field1: "value1"
    - fixed_via_root:
        - [test_binding, ~, my_mixin1, inner] # Qualified this naming the root scope
    - adapting_via_scope:
        - [my_mixin1, ~, inner] # Qualified this naming the reusable scope my_mixin1
    - adapting_lexical:
        - [inner] # Lexical reference to the nearest inner in context

  my_mixin2:
    - [my_mixin1]
    - inner:
        field2: "value2"
```

### 6.2 How Each Reference Resolves

#### 6.2.1 Qualified this naming an outer, absolute scope

- **Reference**: `fixed_via_root` uses `[test_binding, ~, my_mixin1, inner]`, a qualified this that names the outermost scope `test_binding` and then projects `my_mixin1` and `inner` from there.

- **Behavior**: Because it routes through the absolute path from the root, it always reaches the original `test_binding.my_mixin1.inner`, regardless of how `my_mixin1` is later inherited or extended.

- **Result**: `test_binding.my_mixin2.fixed_via_root` contains only `field1`. It reaches the original `my_mixin1.inner` and does not pick up the `field2` added in `my_mixin2.inner`.

#### 6.2.2 Qualified this naming a reusable scope

- **Reference**: `adapting_via_scope` uses `[my_mixin1, ~, inner]`, a qualified this that names the enclosing scope `my_mixin1` and projects `inner` through its dynamic `self`.

- **Behavior**: When `my_mixin2` inherits `my_mixin1`, the dynamic `self` of `my_mixin1` is the merged composition, so `inner` resolves to the merged `inner`.

- **Result**: `test_binding.my_mixin2.adapting_via_scope` contains both `field1` and `field2`.

#### 6.2.3 Lexical reference

- **Reference**: `adapting_lexical` uses `[inner]`, a lexical reference to the nearest `inner` in the current context.

- **Behavior**: When `my_mixin2` inherits `my_mixin1`, the nearest `inner` in context is the merged `inner`.

- **Result**: `test_binding.my_mixin2.adapting_lexical` contains both `field1` and `field2`.

### 6.3 Key Observations

1. **The anchor scope, not a binding time, determines the target.** All three references resolve dynamically against the inherited tree. A qualified this that names the outer, absolute scope (`test_binding`) reaches a fixed target; a qualified this that names a reusable scope (`my_mixin1`), or a lexical reference (`[inner]`), reaches a target that adapts to the current context.

2. **Naming the root gives a fixed target.** `test_binding.my_mixin2.fixed_via_root` includes only `field1` because it routes through `test_binding.my_mixin1`, the original definition, unaffected by `my_mixin2`.

3. **Naming a reusable scope, or a lexical reference, gives an adapting target.** Both `adapting_via_scope` and `adapting_lexical` include `field1` and `field2` because they resolve `inner` in the context of `my_mixin2`, whose `inner` is the merged view.

### 6.4 Practical Guidelines

- **Name an outer, absolute scope** (a qualified this rooted at an enclosing module or the root) when you need a reference to always reach a specific mixin, unaffected by how it is later inherited or extended.

- **Name a reusable scope, or use a lexical reference,** when you want the reference to adapt to the context in which the mixin is reused, for example when building mixins intended for extension where properties may be added or merged.

By understanding these binding rules and how the first segment of an inheritance determines the resolution mechanism, you can design mixins that behave predictably and flexibly, depending on your use case.

## 7. Appendices

This section provides additional resources and references to aid in the understanding of MIXINv2. It includes a JSON Schema reference, which defines the structure of Mixin files, and a glossary of terms used throughout the language specification.

### 7.1 JSON Schema Reference

The JSON Schema that defines the structure of MIXINv2 files is [`mixinv2.schema.json`](https://github.com/Atry/MIXINv2/blob/main/mixinv2.schema.json), maintained at the repository root. It specifies the types and constraints for mixin definitions, including references, qualified `this` references, properties, and inheritance rules. This schema is useful for validating MIXINv2 files to ensure they conform to the expected format. (The core inheritance-calculus, MIXINv2 without its sugar, has its own schema, [`inheritance-calculus.schema.json`](https://github.com/Atry/MIXINv2/blob/main/inheritance-calculus.schema.json).)

#### Explanation of the Schema

- **Reference**:

  - Represents a reference to another mixin or module. Defined as an array of strings. This form is used to point to other mixins within the same file or across files.
  - Example: `[module_name, mixin_name]` or `[file_name, mixin_name]`.

- **Properties**:

  - Represents a collection of property definitions within a mixin. Each property can be another mixin or a scalar value (string, number, boolean, or null).
  - Example:
    ```yaml
    person:
      name: "John Doe"
      age: 30
      is_employed: true
    ```

- **Inheritance and Own Properties**:

  - Represents a combination of references and own property definitions within a mixin. This allows a mixin to inherit from other mixins while also defining its own properties.
  - Example:
    ```yaml
    Car:
      - [Vehicle]
      - model: "Sedan"
      - color: "Blue"
    ```

- **Mixin**:

  - Represents a mixin definition. A mixin can be a reference to another mixin, a set of properties, or a combination of references and properties.

This schema provides a structured way to define and validate mixins in MIXINv2, ensuring consistency and correct syntax across different files and formats.

### 7.2 Glossary

This section provides definitions of key terms used in MIXINv2 specification.

- **Mixin**: The fundamental building block in MIXINv2. It represents a reusable unit that can contain properties, references, or scalar values. Mixins can be inherited, composed, and combined to form complex data structures and logic.

- **Reference**: An array of strings that points to another mixin, indicating the path to the target. A reference is either a lexical reference (an all-string array) or a qualified this reference (a `null`, written `~`, in second position). When a reference appears as a member of a mixin, it drives inheritance.

- **Inheritance**: The deep-merge mechanism by which a mixin combines the properties and scalar values of the mixins that its references resolve to. Inheritance in MIXINv2 is conflict-free, allowing multiple parent mixins to be combined without error.

- **Property**: A named value within a mixin. Properties are named mixins, containing scalar values (e.g., strings, numbers), references to other mixins, or nested properties. Properties define the internal structure or behavior of a mixin.

- **Scalar Value**: A single, indivisible value within a mixin, such as a string, number, boolean, or null. Scalar values can be merged with other properties in a mixin.

- **Lexical Reference**: A reference written as an all-string array. Its first segment climbs outward to the nearest enclosing scope that _defines_ that label, then projects the remaining segments downward. See Section 5.2.1.

- **Qualified This**: A reference whose second element is `null` (written `~`), of the form `[Scope, ~, path...]`. Its first segment names the nearest enclosing scope that _is_ that label, reaching that scope's dynamic `self`, then projects the path. Analogous to Java's `Outer.this`. See Section 5.2.4.

- **Lexical Scope**: The context in which a mixin or property is defined. The lexical scope determines the visibility of mixins and properties within a file, directory, or project.

- **Same-Name Skip Semantics**: A lexical reference resolution rule that prevents self-reference. When the first segment of a reference path matches the defining mixin's own key, the first match found during the upward scope traversal is skipped. This allows a mixin to naturally reference an outer mixin with the same name, similar to how pytest fixtures shadow outer fixtures of the same name. See Section 5.2.1 for details.

- **Directory Scope**: The scope defined by a directory. All mixins within a directory are part of the directory scope, and files within the directory can inherit mixins using the directory scope.

- **Cross-File Inheritance**: Inheriting a mixin defined in a different file, expressed with a reference whose leading segments name the file. MIXINv2 will automatically search for the target mixin within the directory hierarchy.

- **Schema**: A JSON Schema definition that describes the structure of a Mixin file. The schema defines the types, constraints, and relationships between mixins, properties, and references.

- **File Format**: The supported formats for defining MIXINv2 source code. MIXINv2 supports YAML, JSON, and TOML, with restrictions to ensure compatibility with JSON serialization.

- **Naming Convention**: The rules for naming mixins and files in MIXINv2. These conventions help distinguish between type-like mixins, value-like mixins, and instances, and ensure clarity and consistency in code organization.

- **Conflict-Free Inheritance**: MIXINv2's approach to inheritance ensures that properties and scalar values from multiple parents are merged seamlessly without conflicts. This model eliminates issues commonly associated with multiple inheritance in other languages, such as the diamond problem.

- **Property Merging**: The process by which properties with the same name from multiple parent mixins are automatically combined into the inheriting mixin without causing conflicts.

- **Inheritance Hierarchy**: The structure formed by mixins inheriting from other mixins, creating a tree-like or graph-like relationship that defines how properties and inherited members are propagated.
