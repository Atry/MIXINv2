Getting Started with Decorators
================================

The examples below build a single web application step by step, introducing one
concept at a time. All code is runnable with the standard library only.


Step 1 — Define services
------------------------

Decorate a class with ``@scope`` to make it a DI container. Annotate each value with
``@resource`` and expose it with ``@public``. Resources declare their dependencies as
ordinary function parameters; the framework injects them by name.

Use ``@extern`` to declare a dependency that must come from outside the scope — the
equivalent of a pytest fixture parameter. Pass multiple scopes to ``evaluate()`` to
compose them; dependencies are resolved by name across scope boundaries. Config
values are passed as kwargs when calling the evaluated scope.

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_decorator/step1_services.py
   :language: python
   :start-after: # [docs:step1-define-services]
   :end-before: # [/docs:step1-define-services]
   :dedent:

``SQLiteDatabase`` owns ``databasePath``; ``UserRepository`` has no knowledge of the
database layer — it only declares ``connection: sqlite3.Connection`` as a parameter
and receives it automatically from the composed scope.

.. tip:: **Naming convention**

   Throughout this tutorial we use **UpperCamelCase** for scopes and **lowerCamelCase**
   for resources. The idea is that a scope is conceptually a *class* — an instantiable
   container — while a resource is a lazily-evaluated value inside it.

   In the example above, ``SQLiteDatabase`` and ``UserRepository`` are scopes
   (UpperCamelCase), while ``databasePath``, ``connection``, and ``userCount`` are
   resources (lowerCamelCase).

   This convention extends to Python modules used as scopes: a module file representing
   a scope is named in UpperCamelCase (e.g., ``SqliteDatabase.py``), and a subpackage
   representing a nested scope likewise (e.g., ``UserRepository/Request/``). This
   deviates from PEP 8 — the MIXINv2 decorators form a DSL, and the casing signals
   that the code is not plain Python data model.


Step 2 — Layer cross-cutting concerns with ``@patch`` and ``@merge``
--------------------------------------------------------------------

``@patch`` wraps an existing resource value with a transformation. This lets an
add-on scope modify a value without touching the scope that defined it — the same
idea as pytest's ``monkeypatch``, but composable.

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_decorator/step2_patch.py
   :language: python
   :start-after: # [docs:step2-patch]
   :end-before: # [/docs:step2-patch]
   :dedent:

When several independent scopes each contribute a piece to the same resource, use
``@merge`` to define how the contributions are aggregated:

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_decorator/step2_merge.py
   :language: python
   :start-after: # [docs:step2-merge]
   :end-before: # [/docs:step2-merge]
   :dedent:

A ``@patch`` can itself declare ``@extern`` dependencies, which are injected like any
other resource:

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_decorator/step2_patch_extern.py
   :language: python
   :start-after: # [docs:step2-patch-extern]
   :end-before: # [/docs:step2-patch-extern]
   :dedent:


Step 3 — Force evaluation at startup with ``@eager``
-----------------------------------------------------

All resources are lazy by default: computed on first access, then cached for the
lifetime of the scope. Mark a resource ``@eager`` to evaluate it immediately when
``evaluate()`` returns — useful for schema migrations or connection pre-warming that
must complete before the application starts serving requests:

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_decorator/step3_eager.py
   :language: python
   :start-after: # [docs:step3-eager]
   :end-before: # [/docs:step3-eager]
   :dedent:

Without ``@eager``, the ``CREATE TABLE`` would not run until ``root.connection`` is first
accessed.


Step 4 — App scope vs request scope
------------------------------------

So far all resources have had application lifetime: created once at startup and
reused for every request. Real applications also need per-request resources — values
that must be created fresh for each incoming request and discarded when it completes.

A nested ``@scope`` named ``Request`` serves as a per-request factory. The
framework injects it by name as a ``Callable``; calling
``Request(request=handler)`` returns a fresh instance.

The application below has four scopes, each owning only its own concern:

- **SQLiteDatabase** — owns ``databasePath``, provides ``connection``
- **UserRepository** — business logic; owns ``userCount`` and per-request ``currentUser``
- **HttpHandlers** — HTTP layer; owns per-request ``userId``, ``responseBody``, ``responseSent``
- **NetworkServer** — network layer; owns ``host``/``port``, creates the ``HTTPServer``

``UserRepository.Request`` and ``HttpHandlers.Request`` are composed into a
single ``Request`` by the union mount. ``userId`` (extracted from the HTTP path
by ``HttpHandlers.Request``) flows automatically into ``currentUser`` (looked up
in the DB by ``UserRepository.Request``) without any glue code.

``responseSent`` is an IO resource: it sends the HTTP response as a side effect and
returns ``None``. The ``_Handler`` class is defined at module level and accesses the
``Request`` factory through ``self.server.request_scope_factory``; the ``server``
resource stores it on the ``HTTPServer`` instance. The handler body is a single
attribute access; all logic lives in the DI graph. In an async framework (e.g.
FastAPI), return an ``asyncio.Task[None]`` instead of a coroutine, which cannot be
safely awaited in multiple dependents.

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_decorator/step4_http_server.py
   :language: python
   :start-after: # [docs:step4-http-server]
   :end-before: # [/docs:step4-http-server]
   :dedent:

Assemble into a module and evaluate — pass the module directly to ``evaluate()``:

.. code-block:: python

   import mixinv2_examples.app_decorator.step4_http_server as step4_http_server

   root = evaluate(step4_http_server, modules_public=True).App(
       databasePath="/var/lib/myapp/prod.db",
       host="127.0.0.1",
       port=8080,
   )
   server = root.server

Swapping to a test configuration is just different kwargs; no scope or composition changes:

.. code-block:: python

   test_root = evaluate(step4_http_server, modules_public=True).App(
       databasePath=":memory:",  # fresh, isolated database for each test
       host="127.0.0.1",
       port=0,                    # OS assigns a free port
   )
   # test_root.connection  → sqlite3.Connection to :memory:
   # test_root.server      → HTTPServer on OS-assigned port


Decorator reference
-------------------

.. list-table::
   :header-rows: 1
   :widths: 25 75

   * - Decorator
     - Purpose
   * - ``@scope``
     - Define a DI container (class) or sub-namespace
   * - ``@resource``
     - Declare a lazily-computed value; parameters are injected by name
   * - ``@public``
     - Expose a ``@resource`` or ``@scope`` to external callers
   * - ``@extern``
     - Declare a required dependency that must come from the composed scope
   * - ``@patch``
     - Provide a transformation that wraps an existing resource
   * - ``@patch_many``
     - Like ``@patch`` but yields multiple transformations at once
   * - ``@merge``
     - Define how patches are aggregated (e.g. ``frozenset``, ``list``, custom reducer)
   * - ``@eager``
     - Force evaluation at scope creation rather than on first access
   * - ``@extend(*refs)``
     - Inherit from other scopes explicitly (for package-level union mounts)
   * - ``evaluate(*scopes)``
     - Resolve and union-mount one or more scopes into a single dependency graph


Python modules as scopes
-------------------------

The ``@scope`` classes above are a teaching convenience — the real-world style is
plain Python modules, just like pytest fixtures don't require a class. Every
``@scope`` class maps directly to a module file; pass it to ``evaluate()`` the same
way:

.. code-block:: python

   import SqliteDatabase   # SqliteDatabase.py with @extern / @resource / @public
   import UserRepository   # UserRepository/ package

The same decorators work on module-level functions exactly as on class methods. A
subpackage becomes a nested scope — ``UserRepository/Request/`` is the
module equivalent of a nested ``@scope class Request``.

Use ``@extend`` in a package's ``__init__.py`` to declare the composition, then
``evaluate()`` receives the single package:

.. literalinclude:: ../../mixinv2-examples/src/mixinv2_examples/app_di/__init__.py
   :language: python
   :start-after: # [docs:module-extend]
   :end-before: # [/docs:module-extend]

.. code-block:: python

   import myapp

   root = evaluate(myapp, modules_public=True).App(databasePath=":memory:")

Runnable module-based equivalents of all tutorial examples are in
:github:`packages/mixinv2-examples/tests/test_readme_package_examples.py`,
using the fixture package at
:github:`packages/mixinv2-examples/src/mixinv2_examples/app_di/`.
