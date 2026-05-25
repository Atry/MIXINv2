"""TEMPORARY scaffolding: capture the call graph and render an English
numbered-list evaluation trace for the appendix.

The interpreter (mixinv2._core) is instrumented to record, for the query
HasMultipleOuters.outer, every semantic-function call as a node and every
trigger relationship (caller -> callee) as an edge. Nodes are deduplicated
by memoization. We emit one numbered list item per call, in dependency
order (a call appears after the calls it depends on), and each item names,
in English, which earlier items it depends on, how it computes, and what it
yields. Paths are written with full labels.
"""

from collections import deque
from pathlib import Path

import fixtures
import mixinv2_examples
import mixinv2_library
import _trace_patch
from mixinv2._runtime import evaluate

_PREFIX = ("MultipleOuters",)
_OUTPUT = (
    Path(__file__).resolve().parents[3]
    / "inheritance-calculus"
    / "generated-evaluation-trace.tex"
)


def _strip(path: tuple) -> tuple:
    if path[: len(_PREFIX)] == _PREFIX:
        return path[len(_PREFIX) :]
    return path


def _under(value) -> bool:
    return isinstance(value, tuple) and value[: len(_PREFIX)] == _PREFIX


def _mathlabel(segment) -> str:
    # A metalanguage label: a quoted string literal, so it is never mistaken
    # for a metalanguage variable. Renders as "segment" in upright type.
    return rf"\text{{``{segment}''}}"


def _path(path: tuple) -> str:
    """A metalanguage path: a tuple of quoted labels, e.g. (``A'', ``B'');
    the root path is ()."""
    path = _strip(path)
    if not path:
        return "()"
    return "(" + ", ".join(_mathlabel(s) for s in path) + ")"


def _path_text(path: tuple) -> str:
    """Same as _path but wrapped in inline math for prose."""
    return f"${_path(path)}$"


def _node_relevant(fields) -> bool:
    for key in ("path", "site", "origin", "def_site"):
        if _under(fields.get(key)):
            return True
    v = fields.get("frontier_in")
    if isinstance(v, tuple) and any(_under(p) for p in v):
        return True
    return False


def _collect_graph():
    nodes = {
        nid: f for nid, f in _trace_patch.NODES.items() if _node_relevant(f)
    }
    edges = [
        (a, b) for (a, b) in _trace_patch.EDGES if a in nodes and b in nodes
    ]
    return nodes, edges


_QUERY_SUPERS = ("supers", "('MultipleOuters', 'HasMultipleOuters', 'outer')")


def _reachable(root, edges):
    adjacency: dict = {}
    for a, b in edges:
        adjacency.setdefault(a, []).append(b)
    seen = {root}
    queue = deque([root])
    while queue:
        node = queue.popleft()
        for nxt in adjacency.get(node, ()):
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def _topo_order(keep, edges):
    """Order so that every dependency (callee) precedes its caller.

    Edge (caller, callee) means caller depends on callee, so callee must come
    first. We do a DFS post-order from the query root over caller->callee
    edges; post-order visits callees before callers.
    """
    adjacency: dict = {}
    for a, b in edges:
        if a in keep and b in keep:
            adjacency.setdefault(a, []).append(b)
    order: list = []
    visited: set = set()
    on_stack: set = set()

    def visit(node):
        if node in visited:
            return
        visited.add(node)
        on_stack.add(node)
        for nxt in adjacency.get(node, ()):
            if nxt not in on_stack:  # break cycles defensively
                visit(nxt)
        on_stack.discard(node)
        order.append(node)

    # Start from the query root so its whole dependency cone is ordered.
    visit(_QUERY_SUPERS)
    # Any remaining kept nodes not reachable: append in stable order.
    for nid in keep:
        if nid not in visited:
            visit(nid)
    return order


import re as _re


def _label_for(nid) -> str:
    """A stable LaTeX label key for a call-graph node."""
    raw = f"{nid[0]}-{nid[1]}"
    raw = raw.replace("MultipleOuters", "")
    sanitized = _re.sub(r"[^A-Za-z0-9]+", "-", raw).strip("-")
    return f"trace:{sanitized}"


def _refs(dep_nids, order):
    """Render dependency cross-references as \\ref{} in trace order."""
    if not dep_nids:
        return ""
    ordered = [nid for nid in order if nid in dep_nids]
    refs = [rf"\ref{{{_label_for(nid)}}}" for nid in ordered]
    if len(refs) == 1:
        return f"item~{refs[0]}"
    return "items~" + ", ".join(refs[:-1]) + f" and~{refs[-1]}"


def _path_set(paths) -> str:
    return "\\{" + ", ".join(_path(p) for p in paths) + "\\}"


def _pair_set(pairs) -> str:
    return "\\{" + ", ".join(
        f"({_path(site)}, {_path(override)})" for site, override in pairs
    ) + "\\}"


def _describe(nid, fields, dep_nids, order, resolve_label_of) -> str:
    """English description of one semantic-function call: dependencies, how it
    computes, and the result it yields."""
    fn = fields["function"]
    ref = _refs(dep_nids, order)
    deps_clause = f" using {ref}" if ref else ""

    if fn == "overrides":
        p = _path_text(fields["path"])
        result = _path_set(fields.get("result", ()))
        return (
            f"Compute $\\overrides({_path(fields['path'])})$, the paths "
            f"sharing the identity of {p}{deps_clause}. "
            f"It keeps {p} and adds any same-label definition reached through "
            f"the supers of its enclosing scope. "
            f"Result: ${result}$."
        )
    if fn == "bases":
        p = _path_text(fields["path"])
        refs = fields.get("references", ())
        if not refs:
            return (
                f"Compute $\\bases({_path(fields['path'])})$. "
                f"{p} carries no inheritance reference "
                f"($\\inherits = \\varnothing$), so it has no direct base. "
                f"Result: $\\varnothing$."
            )
        ref_strs = "; ".join(
            f"the reference pair $({r['n']}, {_down_math(r['down'])})$ "
            f"(take {_steps(r['n'])} upward, then project {_down(r['down'])})"
            for r in refs
        )
        resolve_ref = resolve_label_of.get(nid)
        target_clause = (
            f"whose target is obtained by item~\\ref{{{resolve_ref}}}"
            if resolve_ref
            else "whose target is obtained by the corresponding $\\resolve$ step"
        )
        return (
            f"Compute $\\bases({_path(fields['path'])})$. "
            f"{p} carries {ref_strs}, {target_clause}."
        )
    if fn == "resolve":
        targets = fields.get("targets")
        result = (
            f" Result: ${_path_set(targets)}$." if targets is not None else ""
        )
        return (
            f"Compute $\\resolve$ for the reference pair "
            f"$({fields['n']}, {_down_math(fields['down'])})$ defined at "
            f"{_path_text(fields['origin'])}, reached from inheritance site "
            f"{_path_text(fields['site'])}{deps_clause}. "
            f"It takes {_steps(fields['n'])} upward through $\\this$ and then "
            f"appends the projection.{result}"
        )
    if fn == "this":
        fin = ", ".join(_path(p) for p in fields["frontier_in"])
        fout = fields.get("frontier_out")
        result = (
            f" Result: ${_path_set(fout)}$." if fout is not None else ""
        )
        return (
            f"Compute one $\\this$ step{deps_clause}: from the frontier "
            f"$\\{{{fin}\\}}$, take the supers of each frontier path and keep "
            f"those whose definition site is {_path_text(fields['def_site'])}, "
            f"collecting their inheritance sites as the new frontier.{result}"
        )
    if fn == "supers":
        p = _path_text(fields["path"])
        pairs = fields.get("pairs")
        result = (
            f" Result: ${_pair_set(pairs)}$." if pairs is not None else ""
        )
        return (
            f"Compute $\\supers({_path(fields['path'])})${deps_clause}. "
            f"It takes the reflexive-transitive closure of $\\bases$ from {p}, "
            f"pairing each reachable override with the inheritance site through "
            f"which it is reached.{result}"
        )
    return fn


def _down(down: tuple) -> str:
    if not down:
        return "the empty projection"
    return "$" + _down_math(down) + "$"


def _down_math(down: tuple) -> str:
    """The downward-projection list as a bare math sequence for use inside a
    reference pair (n, down)."""
    if not down:
        return "()"
    return "(" + ", ".join(_mathlabel(d) for d in down) + ")"


def _steps(n: int) -> str:
    if n == 0:
        return "no step"
    if n == 1:
        return "one step"
    return f"{n} steps"


def test_generate_numbered_trace() -> None:
    _trace_patch.reset()
    _trace_patch.install()
    _trace_patch.ENABLED = True
    try:
        root = evaluate(
            mixinv2_library, mixinv2_examples, fixtures, modules_public=True
        )
        _ = root.MultipleOuters.HasMultipleOuters.outer
    finally:
        _trace_patch.ENABLED = False
        _trace_patch.uninstall()

    nodes, edges = _collect_graph()
    assert _QUERY_SUPERS in nodes, "query supers node missing"

    # Merge result fields from the linear records into the node fields, so each
    # node carries everything needed to describe its result. Node ids match the
    # ids built by the trace_frame wrappers in _trace_patch. A resolve record is
    # immediately followed by a resolve_result record carrying its targets.
    last_resolve_nid = None
    for record in _trace_patch.RECORDS:
        fn = record["function"]
        if fn in ("overrides", "bases", "supers"):
            nid = (fn, str(record["path"]))
        elif fn == "resolve":
            nid = (
                "resolve",
                f"{record['site']}|{record['origin']}|{record['n']}"
                f"|{record['down']}",
            )
            last_resolve_nid = nid
        elif fn == "resolve_result":
            if last_resolve_nid in nodes:
                nodes[last_resolve_nid]["targets"] = record["targets"]
            continue
        elif fn == "this":
            nid = (
                "this",
                f"{record['frontier_in']}|{record['def_site']}"
                f"|{record['remaining']}",
            )
        else:
            continue
        if nid in nodes:
            for key, value in record.items():
                if key != "function":
                    nodes[nid][key] = value

    keep = _reachable(_QUERY_SUPERS, edges)
    order = _topo_order(keep, edges)

    # caller -> callees, restricted to kept nodes
    deps: dict = {}
    for a, b in edges:
        if a in keep and b in keep:
            deps.setdefault(a, set()).add(b)

    # Map each bases node to the resolve node that resolves its reference,
    # matched by origin (= the bases path) and n/down of the reference.
    resolve_by_origin: dict = {}
    for nid, f in nodes.items():
        if nid[0] == "resolve":
            key = (f["origin"], f["n"], tuple(f["down"]))
            resolve_by_origin[key] = nid
    resolve_label_of: dict = {}
    for nid, f in nodes.items():
        if nid[0] == "bases":
            parent = f["path"][:-1]  # origin of the reference = init(path)
            for r in f.get("references", ()):
                key = (parent, r["n"], tuple(r["down"]))
                if key in resolve_by_origin:
                    resolve_label_of[nid] = _label_for(resolve_by_origin[key])

    lines = [r"\begin{enumerate}"]
    for nid in order:
        dep_nids = deps.get(nid, set())
        text = _describe(nid, nodes[nid], dep_nids, order, resolve_label_of)
        lines.append(rf"  \item \label{{{_label_for(nid)}}}{text}")

    # Final item: properties of the query, derived from the last supers.
    query = ("MultipleOuters", "HasMultipleOuters", "outer")
    lines.append(
        rf"  \item \label{{trace:properties}}Compute "
        rf"$\properties({_path(query)})$ using "
        rf"item~\ref{{{_label_for(_QUERY_SUPERS)}}}. "
        rf"It unions the $\defines$ of every override path in that $\supers$ "
        rf"set. Only ${_path(('MultipleOuters', 'MyOuter'))}$ defines a "
        rf"label, namely ${_mathlabel('MyInner')}$, reached through both "
        rf"${_path(('MultipleOuters', 'Object1'))}$ and "
        rf"${_path(('MultipleOuters', 'Object2'))}$; set union collapses the "
        rf"two routes. Result: $\{{{_mathlabel('MyInner')}\}}$."
    )
    lines.append(r"\end{enumerate}")

    _OUTPUT.write_text("\n".join(lines) + "\n")
    print(f"Wrote {len(order) + 1} items to {_OUTPUT}")
    # Sanity: the query supers item must be last among captured calls, and the
    # crux this step must yield two targets.
    assert order[-1] == _QUERY_SUPERS, "query supers should be last in topo order"
    crux = [
        nid
        for nid in order
        if nid[0] == "this"
        and len(nodes[nid].get("frontier_out", ())) == 2
    ]
    assert crux, "expected a two-target this step"
