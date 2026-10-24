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
    / "paper"
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


def _eq_block(lhs: str, elements: list) -> str:
    """A displayed equation stating a call and its result, appended after the
    prose of a trace item.

    For zero or one element the result is inline. For two or more it is
    stacked one per line, and the equation breaks after the equals sign so
    that a long left-hand side does not push the stacked set off the right
    margin.
    """
    if not elements:
        return f"\n  \\[\n    {lhs} = \\varnothing\n  \\]"
    if len(elements) == 1:
        return f"\n  \\[\n    {lhs} = \\{{{elements[0]}\\}}\n  \\]"
    rows = [f"&{e}," for e in elements[:-1]] + [f"&{elements[-1]}"]
    body = " \\\\\n          ".join(rows)
    inner = (
        "\\left\\{\\begin{aligned}\n          "
        + body
        + "\n        \\end{aligned}\\right\\}"
    )
    return (
        "\n  \\[\n"
        "    \\begin{aligned}\n"
        f"      &{lhs} ={{}} \\\\\n"
        f"      &\\quad {inner}\n"
        "    \\end{aligned}\n"
        "  \\]"
    )


def _describe(nid, fields, dep_nids, order, resolve_label_of) -> str:
    """English description of one semantic-function call: dependencies, how it
    computes, and the result it yields."""
    fn = fields["function"]
    ref = _refs(dep_nids, order)
    deps_clause = f" using {ref}" if ref else ""

    if fn == "overrides":
        path_math = _path(fields["path"])
        p = _path_text(fields["path"])
        elems = [_path(q) for q in fields.get("result", ())]
        prose = (
            f"Compute $\\overrides({path_math})$, the paths "
            f"sharing the identity of {p}{deps_clause}. "
            f"It keeps {p} and adds any same-label definition reached through "
            f"the supers of its enclosing scope:"
        )
        return prose + _eq_block(f"\\overrides({path_math})", elems)
    if fn == "bases":
        path_math = _path(fields["path"])
        p = _path_text(fields["path"])
        targets = fields.get("eq_bases") or []
        prose = (
            f"Compute $\\bases({path_math})${deps_clause}. "
            f"It resolves the references carried by the overrides of {p} at the "
            f"enclosing scope, and collects their targets:"
        )
        return prose + _eq_block(
            f"\\bases({path_math})", [_path(t) for t in targets]
        )
    if fn == "resolve":
        targets = fields.get("targets")
        prose = (
            f"Compute $\\resolve$ for the reference pair "
            f"$({fields['n']}, {_down_math(fields['down'])})$ defined at "
            f"{_path_text(fields['origin'])}, reached from inheritance site "
            f"{_path_text(fields['site'])}{deps_clause}. "
            f"It takes {_steps(fields['n'])} upward through $\\this$ and then "
            f"appends the projection"
        )
        if targets is None:
            return prose + "."
        lhs = (
            f"\\resolve({_path(fields['site'])}, {_path(fields['origin'])}, "
            f"{fields['n']}, {_down_math(fields['down'])})"
        )
        return prose + ":" + _eq_block(lhs, [_path(t) for t in targets])
    if fn == "this":
        fin = ", ".join(_path(p) for p in fields["frontier_in"])
        fout = fields.get("frontier_out")
        prose = (
            f"Compute one $\\this$ step{deps_clause}: from the frontier "
            f"$\\{{{fin}\\}}$, take the supers of each frontier path and keep "
            f"those whose definition site is {_path_text(fields['def_site'])}, "
            f"collecting their inheritance sites as the new frontier"
        )
        if fout is None:
            return prose + "."
        lhs = (
            f"\\this(\\{{{fin}\\}}, {_path(fields['def_site'])}, "
            f"{fields['remaining']})"
        )
        return prose + ":" + _eq_block(lhs, [_path(p) for p in fout])
    if fn == "supers":
        path_math = _path(fields["path"])
        p = _path_text(fields["path"])
        pairs = fields.get("pairs")
        prose = (
            f"Compute $\\supers({path_math})${deps_clause}. "
            f"It takes the reflexive-transitive closure of $\\bases$ from {p}, "
            f"pairing each reachable override with the inheritance site through "
            f"which it is reached"
        )
        if pairs is None:
            return prose + "."
        elems = [f"({_path(s)}, {_path(o)})" for s, o in pairs]
        return prose + ":" + _eq_block(f"\\supers({path_math})", elems)
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


def _sym_at(root_symbol, full_path):
    """Navigate the root MixinSymbol to a full (unstripped) path via .get."""
    s = root_symbol
    for key in full_path:
        s = s.get(key)
        if s is None:
            return None
    return s


def _eq_bases(root_symbol, full_path):
    """Compute the paper's bases(p) (equation eq:bases): the union, over every
    override o of p and every reference r that o carries, of resolving r at the
    enclosing scope init(p). This is what the appendix's trace should show for a
    bases node; the interpreter instead exposes per-node own references
    (normalized_references), which is not eq:bases for an inherited override.
    Returns a sorted list of stripped target paths, or None if p is unreachable.
    """
    p_sym = _sym_at(root_symbol, full_path)
    site = _sym_at(root_symbol, full_path[:-1])
    if p_sym is None or site is None:
        return None
    targets: list = []
    seen: set = set()
    for override in p_sym.overrides:
        for reference in override.normalized_references:
            for target in reference.get_symbols(site):
                stripped = _strip(tuple(target.path))
                if stripped not in seen:
                    seen.add(stripped)
                    targets.append(stripped)
    return sorted(targets)


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

    # For each bases node, compute the paper's eq:bases value (overrides expanded
    # and their references resolved at the enclosing scope), not the interpreter's
    # per-node own references. Computed after uninstall, so it is untraced.
    for nid, node_fields in nodes.items():
        if nid[0] == "bases":
            node_fields["eq_bases"] = _eq_bases(root.symbol, node_fields["path"])

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

    # Final item: membership point query for the label MyInner at the query
    # path, decided from the last supers (membership is supers(p . l) != empty).
    query = ("MultipleOuters", "HasMultipleOuters", "outer")
    query_inner = query + ("MyInner",)
    my_outer = ("MultipleOuters", "MyOuter")
    my_outer_inner = ("MultipleOuters", "MyOuter", "MyInner")
    obj1 = _path(("MultipleOuters", "Object1"))
    obj2 = _path(("MultipleOuters", "Object2"))
    witness = (
        "\n  \\[\n"
        "    \\begin{aligned}\n"
        f"      &(\\_,\\; {_path(my_outer)}) \\in \\supers({_path(query)}), \\\\\n"
        f"      &{_path(my_outer_inner)} \\in \\dom(\\inherits), \\\\\n"
        f"      &\\quad \\text{{reached through }} {obj1} \\text{{ and }} {obj2}, \\\\\n"
        f"      &\\supers({_path(query_inner)}) \\neq \\varnothing.\n"
        "    \\end{aligned}\n"
        "  \\]\n  "
    )
    lines.append(
        rf"  \item \label{{trace:property}}Decide whether "
        rf"${_mathlabel('MyInner')}$ is a property at {_path_text(query)}, that is, "
        rf"whether the path {_path_text(query_inner)} exists. "
        rf"Item~\ref{{{_label_for(_QUERY_SUPERS)}}} exhibits a witnessing override:"
        + witness
        + rf"so ${_mathlabel('MyInner')}$ is a property at {_path_text(query)}."
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
