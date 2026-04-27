#!/usr/bin/env python3
"""tools/dep_graph.py — auto-generate a dependency graph of `@[stat_lemma]`
(and `@[stats_ineq]`, `@[prob_simp]`) tagged theorems across `Pythia/`.

The goal is contributor onboarding: a new external contributor wants to
know which top-level theorems depend on which low-level tagged lemmas,
so they can pick a target they can actually close. Today they would
have to grep through `Pythia/*` by hand.

This script walks the Lean tree and emits a Mermaid (`graph TD`) or DOT
(`digraph`) definition. Nodes are theorem names; edges point from caller
to callee. Nodes are color-coded by tag.

Caveat: extraction is **textual / heuristic**, not LSP-based. We look
for the literal attribute `@[stat_lemma]` (or the other two) on its own
line, find the next `theorem` or `lemma` declaration, capture its body
up to the next top-level declaration / namespace boundary, and then
scan the body for occurrences of any other tagged-theorem name (word-
bounded). False positives are possible: a theorem can mention another
tagged theorem in a comment, or a name can collide with an unrelated
local. False negatives are also possible: cross-module references that
require namespace-qualified resolution will be missed when the caller
uses an unqualified `open Pythia` import.

LSP-based extraction (querying `lean-lsp-mcp` for `references` or
`lean_local_search` per theorem) is the v2 follow-up. The textual graph
is good enough for contributor onboarding today.

Usage:

    python3 tools/dep_graph.py
    python3 tools/dep_graph.py --output docs/dep_graph.md
    python3 tools/dep_graph.py --format dot --output dep_graph.dot
    python3 tools/dep_graph.py --filter '^Bio'
    python3 tools/dep_graph.py --max-depth 2
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PYTHIA_DIR = REPO_ROOT / "Pythia"

# Recognised attribute tags. Order is presentation-stable: it
# determines legend ordering in the output.
KNOWN_TAGS: tuple[str, ...] = ("stat_lemma", "stats_ineq", "prob_simp")

# Mermaid node color per tag (hex without leading `#`).
TAG_COLOR: dict[str, str] = {
    "stat_lemma": "5DA9E9",   # blue
    "stats_ineq": "F4A261",   # orange
    "prob_simp": "8AC926",    # green
}

# Regex: an attribute line of the form `@[stat_lemma]` (potentially
# combined with other attributes, e.g. `@[stat_lemma, simp]`).
_ATTR_RE = re.compile(r"^\s*@\[([^\]]+)\]\s*$")

# Regex: a theorem / lemma declaration header line. Captures the name.
# Names are Lean identifiers (letters, digits, underscore, dot, `'`).
_DECL_RE = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.']*)\b")


@dataclass(frozen=True)
class TaggedTheorem:
    """One tagged theorem extracted from a `.lean` file.

    `name` is the bare declaration name (no namespace prefix).
    `tags` is the set of recognised attributes that decorate it.
    `body` is the raw text of the declaration block (statement +
    proof), used for downstream textual reference matching.
    `path` is the source file the declaration came from, relative
    to the repo root when possible (else absolute).
    """
    name: str
    tags: frozenset[str]
    body: str
    path: str
    line: int


@dataclass
class DepGraph:
    """An extracted dependency graph.

    Nodes are tagged theorem names; `nodes[name] = TaggedTheorem`.
    `edges` are (caller, callee) pairs where the caller's body
    textually references the callee's name. Edges are deduplicated.
    """
    nodes: dict[str, TaggedTheorem] = field(default_factory=dict)
    edges: set[tuple[str, str]] = field(default_factory=set)


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------


def _strip_comments(text: str) -> str:
    """Remove Lean line comments (`--`) and block comments (`/- ... -/`).

    The dep graph cares about real declaration references, not name
    mentions in docstrings. Stripping comments before name matching
    keeps the edge set honest.

    Block-doc comments `/-- ... -/` are also stripped: doc strings
    routinely cite related theorems for the human reader, and we do
    not want those citations to materialise as graph edges.
    """
    # Strip block comments first (greedy boundary handled by lazy `*?`).
    no_block = re.sub(r"/-.*?-/", " ", text, flags=re.DOTALL)
    # Strip line comments.
    no_line = re.sub(r"--[^\n]*", "", no_block)
    return no_line


def _split_attr_list(attr_text: str) -> list[str]:
    """Split the inside of `@[a, b c, d]` into individual tag names.

    Lean allows compound attribute lists like `@[stat_lemma, simp]`
    or `@[simp, stat_lemma]`. We keep only the bare attribute names
    (drop arguments). Whitespace and trailing args after a space are
    discarded so `simp ↓` becomes `simp`.
    """
    raw_parts = [p.strip() for p in attr_text.split(",")]
    out: list[str] = []
    for part in raw_parts:
        if not part:
            continue
        # An attribute can carry args, e.g. `simp ↓`. We only need the head.
        head = part.split()[0]
        out.append(head)
    return out


def _next_decl_line(
    lines: list[str],
    start: int,
) -> tuple[int, str] | None:
    """Find the next `theorem` / `lemma` decl line after `start`.

    Returns `(line_index, name)` or `None`. Skips intervening attribute
    lines and blank lines: a real-world tagged theorem looks like:

        @[stat_lemma]
        @[reducible]      -- maybe more attributes
        theorem foo ...
    """
    n = len(lines)
    i = start
    while i < n:
        line = lines[i]
        # Allow attribute lines and blank lines between attr and decl.
        if _ATTR_RE.match(line) or line.strip() == "":
            i += 1
            continue
        m = _DECL_RE.match(line)
        if m:
            return i, m.group(2)
        # Non-decl, non-attr, non-blank line means the attribute was
        # not followed by a theorem (e.g. a `def`, `instance`,
        # `structure`). Bail; not a tagged theorem for our purposes.
        return None
    return None


def _capture_body(
    lines: list[str],
    decl_line: int,
) -> str:
    """Capture the body of a declaration starting at `decl_line`.

    The body extends from the declaration header through the proof
    until either:
        * the next top-level `@[...]` attribute or `theorem` / `lemma`
          / `def` / `namespace` / `end` / `section` declaration, or
        * end of file.

    We take a conservative whitespace-aware approach: any line that
    starts at column 0 with one of those keywords ends the body.
    """
    n = len(lines)
    end = n
    boundary = re.compile(
        r"^\s*(@\[|theorem\b|lemma\b|def\b|abbrev\b|structure\b|class\b|"
        r"instance\b|namespace\b|end\b|section\b)"
    )
    for j in range(decl_line + 1, n):
        if boundary.match(lines[j]):
            end = j
            break
    return "\n".join(lines[decl_line:end])


def parse_file(path: Path) -> list[TaggedTheorem]:
    """Extract every tagged theorem from a single `.lean` file.

    Walks the file looking for `@[...]` lines whose attribute list
    contains any of `KNOWN_TAGS`. For each such hit, records the
    next `theorem` / `lemma` declaration as a `TaggedTheorem`.
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    text = _strip_comments(text)
    lines = text.splitlines()
    out: list[TaggedTheorem] = []
    n = len(lines)
    i = 0
    while i < n:
        m = _ATTR_RE.match(lines[i])
        if not m:
            i += 1
            continue
        tags = set(_split_attr_list(m.group(1))) & set(KNOWN_TAGS)
        if not tags:
            i += 1
            continue
        nxt = _next_decl_line(lines, i + 1)
        if nxt is None:
            i += 1
            continue
        decl_line, name = nxt
        body = _capture_body(lines, decl_line)
        try:
            rel = str(path.relative_to(REPO_ROOT))
        except ValueError:
            rel = str(path)
        out.append(TaggedTheorem(
            name=name,
            tags=frozenset(tags),
            body=body,
            path=rel,
            line=decl_line + 1,
        ))
        i = decl_line + 1
    return out


def walk_pythia(root: Path) -> list[TaggedTheorem]:
    """Walk a Pythia/ tree and parse every `.lean` file.

    Files are visited in sorted order so the output is deterministic
    regardless of filesystem iteration order.
    """
    out: list[TaggedTheorem] = []
    for f in sorted(root.rglob("*.lean")):
        out.extend(parse_file(f))
    return out


# ---------------------------------------------------------------------------
# Edge extraction
# ---------------------------------------------------------------------------


def build_graph(theorems: Iterable[TaggedTheorem]) -> DepGraph:
    """Build a dep graph from a flat list of tagged theorems.

    For each theorem `T` and each other tagged theorem `U`, add an
    edge `T -> U` if `U.name` appears as a whole word in `T.body`.
    Self-references (`T -> T`) are dropped.

    Disambiguates name collisions: when two tagged theorems share the
    same simple name (which Lean does allow across namespaces), we
    keep the first-seen entry in the node table; the body matcher
    will still link to that entry. Collisions are rare in practice
    and we accept the minor undercount as the price of a textual
    extractor.
    """
    g = DepGraph()
    for t in theorems:
        if t.name in g.nodes:
            # Name collision: drop. We prefer the first-seen wins
            # rule so the graph is stable under re-runs.
            continue
        g.nodes[t.name] = t

    # Pre-compile a single regex per name for speed.
    name_res = {
        name: re.compile(rf"\b{re.escape(name)}\b")
        for name in g.nodes
    }
    for caller_name, caller in g.nodes.items():
        for callee_name, pat in name_res.items():
            if callee_name == caller_name:
                continue
            if pat.search(caller.body):
                g.edges.add((caller_name, callee_name))
    return g


def filter_graph(g: DepGraph, pattern: str) -> DepGraph:
    """Restrict the graph to nodes whose name OR file path matches `pattern`.

    Path-prefix matching is what most contributors actually want
    (`--filter '^Bio'` = "show me only Bio.* theorems"), but we also
    match against the name itself for symmetry with theorem-level
    targeting. Edges are kept only when both endpoints survive.
    """
    rx = re.compile(pattern)
    keep = {
        name
        for name, t in g.nodes.items()
        if rx.search(name) or rx.search(t.path)
    }
    out = DepGraph()
    out.nodes = {n: g.nodes[n] for n in keep}
    out.edges = {(a, b) for (a, b) in g.edges if a in keep and b in keep}
    return out


def limit_depth(g: DepGraph, max_depth: int) -> DepGraph:
    """Keep only edges within `max_depth` of a root.

    A "root" is a node with no incoming edges (nothing depends on it).
    From each root we follow outgoing edges up to `max_depth` hops,
    keeping every visited edge. Nodes outside that frontier are
    dropped entirely.

    `max_depth = 0` is a no-op (the full graph is returned). Negative
    depths are treated as 0.
    """
    if max_depth <= 0:
        return g
    in_deg: dict[str, int] = {n: 0 for n in g.nodes}
    for _, b in g.edges:
        in_deg[b] = in_deg.get(b, 0) + 1
    roots = [n for n, d in in_deg.items() if d == 0]
    # If every node has an incoming edge (cycle? rare for theorems),
    # use all nodes as roots so the output is non-empty.
    if not roots:
        roots = list(g.nodes)

    adj: dict[str, list[str]] = {n: [] for n in g.nodes}
    for a, b in g.edges:
        adj[a].append(b)

    keep_nodes: set[str] = set()
    keep_edges: set[tuple[str, str]] = set()
    for root in roots:
        # Standard BFS, depth-bounded.
        frontier: list[tuple[str, int]] = [(root, 0)]
        seen = {root}
        keep_nodes.add(root)
        while frontier:
            node, depth = frontier.pop(0)
            if depth >= max_depth:
                continue
            for nxt in adj.get(node, ()):
                keep_edges.add((node, nxt))
                keep_nodes.add(nxt)
                if nxt not in seen:
                    seen.add(nxt)
                    frontier.append((nxt, depth + 1))

    out = DepGraph()
    out.nodes = {n: g.nodes[n] for n in keep_nodes if n in g.nodes}
    out.edges = {
        (a, b) for (a, b) in keep_edges if a in out.nodes and b in out.nodes
    }
    return out


# ---------------------------------------------------------------------------
# Emitters
# ---------------------------------------------------------------------------


def _primary_tag(t: TaggedTheorem) -> str:
    """Pick a single tag for color coding when a theorem has several.

    KNOWN_TAGS is presentation-stable; we pick the first one in that
    list that the theorem carries. So a theorem tagged
    `@[stat_lemma, prob_simp]` colors as a `stat_lemma`.
    """
    for tag in KNOWN_TAGS:
        if tag in t.tags:
            return tag
    # Defensive: should never hit since parse_file filters on KNOWN_TAGS.
    return KNOWN_TAGS[0]


def emit_mermaid(g: DepGraph) -> str:
    """Emit a Mermaid `graph TD` block.

    Output is wrapped in a fenced code block tagged `mermaid` so it
    renders inline on GitHub. Nodes carry `style` directives for
    color coding. Edges are sorted for determinism.
    """
    lines: list[str] = ["```mermaid", "graph TD"]
    # Node declarations + style. Sort for determinism.
    for name in sorted(g.nodes):
        t = g.nodes[name]
        lines.append(f"  {name}[\"{name}\"]")
    for name in sorted(g.nodes):
        t = g.nodes[name]
        color = TAG_COLOR[_primary_tag(t)]
        lines.append(f"  style {name} fill:#{color},stroke:#333,color:#000")
    # Edges.
    for a, b in sorted(g.edges):
        lines.append(f"  {a} --> {b}")
    lines.append("```")
    return "\n".join(lines) + "\n"


def emit_dot(g: DepGraph) -> str:
    """Emit a Graphviz `digraph` block.

    DOT is the canonical academic graph format; we keep it as a
    second-class citizen (`--format dot`) so contributors who want
    to post-process via `dot -Tsvg` have a clean entry point.
    """
    lines = ["digraph dep_graph {", "  rankdir=TD;",
             "  node [shape=box, style=filled];"]
    for name in sorted(g.nodes):
        t = g.nodes[name]
        color = TAG_COLOR[_primary_tag(t)]
        lines.append(
            f"  \"{name}\" [fillcolor=\"#{color}\"];"
        )
    for a, b in sorted(g.edges):
        lines.append(f"  \"{a}\" -> \"{b}\";")
    lines.append("}")
    return "\n".join(lines) + "\n"


def _legend_markdown() -> str:
    """Return a small color legend rendered in Markdown.

    Mermaid does not natively emit a swatch legend, so we hand-roll
    one. Uses HTML span with an inline background so it renders the
    same on GitHub and on local Markdown viewers.
    """
    rows = ["| tag | color |", "|-----|-------|"]
    for tag in KNOWN_TAGS:
        color = TAG_COLOR[tag]
        rows.append(
            f"| `@[{tag}]` | "
            f"<span style=\"background:#{color}\">&nbsp;&nbsp;&nbsp;&nbsp;</span> "
            f"#{color} |"
        )
    return "\n".join(rows) + "\n"


def emit_markdown_document(g: DepGraph) -> str:
    """Wrap a Mermaid graph in a Markdown document with preamble.

    Used as the default output when targeting `docs/dep_graph.md`.
    The preamble warns hand-editors off and points to the regen
    command so the workflow stays a single-source-of-truth.
    """
    parts: list[str] = []
    parts.append("# Pythia theorem dependency graph\n")
    parts.append(
        "Auto-generated by `tools/dep_graph.py`. "
        "Regenerate via the same command. Do not hand-edit.\n"
    )
    parts.append(
        f"Tagged theorems: **{len(g.nodes)}**. "
        f"Edges (caller depends on callee): **{len(g.edges)}**.\n"
    )
    parts.append("## Legend\n")
    parts.append(_legend_markdown())
    parts.append("## Graph\n")
    parts.append(emit_mermaid(g))
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        prog="dep_graph",
        description=(
            "Auto-generate a dependency graph of @[stat_lemma]-tagged "
            "(and @[stats_ineq], @[prob_simp]) theorems across Pythia/."
        ),
    )
    p.add_argument(
        "--root", default=str(DEFAULT_PYTHIA_DIR),
        help="Directory to walk (default: repo's Pythia/).",
    )
    p.add_argument(
        "--format", choices=["mermaid", "dot"], default="mermaid",
        help=(
            "Output format. Mermaid renders inline on GitHub; DOT is "
            "the second-class option for `dot -Tsvg` post-processing."
        ),
    )
    p.add_argument(
        "--output", default=None,
        help=(
            "Destination file. If omitted, print to stdout. When the "
            "filename ends in .md and --format is mermaid, the output "
            "is wrapped in a documented Markdown report."
        ),
    )
    p.add_argument(
        "--filter", default=None,
        help=(
            "Regex applied to theorem name OR source file path. "
            "Edges are kept only when both endpoints match."
        ),
    )
    p.add_argument(
        "--max-depth", type=int, default=0,
        help=(
            "Limit transitive reach from each root. 0 (default) keeps "
            "the full graph."
        ),
    )
    args = p.parse_args(argv)

    root = Path(args.root)
    if not root.is_dir():
        print(f"dep_graph: not a directory: {root}", file=sys.stderr)
        return 2

    theorems = walk_pythia(root)
    graph = build_graph(theorems)
    if args.filter:
        graph = filter_graph(graph, args.filter)
    if args.max_depth:
        graph = limit_depth(graph, args.max_depth)

    if args.format == "dot":
        out = emit_dot(graph)
    else:
        if args.output and args.output.endswith(".md"):
            out = emit_markdown_document(graph)
        else:
            out = emit_mermaid(graph)

    if args.output:
        Path(args.output).write_text(out, encoding="utf-8")
    else:
        sys.stdout.write(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
