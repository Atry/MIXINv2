# fixpoints

Least-fixpoint cached-property infrastructure for mutual recursion.

`fixpoints` provides `fixpoint_cached_property` and `fixpoint_dependent`, drop-in
replacements for `functools.cached_property` that resolve mutually recursive
computations by least-fixpoint iteration. When reentry (a cycle) is detected, the
outermost caller drives a digest loop that re-evaluates participants until their
values stabilize, starting from a configurable bottom value.

This package depends only on the Python standard library.
