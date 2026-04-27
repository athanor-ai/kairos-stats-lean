#!/usr/bin/env python3
"""tools/sim/test_dep_graph.py — pure-Python tests for tools/dep_graph.py.

Builds a synthetic Pythia/ tree under tmp_path, parses it, and asserts
on the extracted graph + emitted Mermaid / DOT. Offline, deterministic,
no Lean toolchain required.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path
from textwrap import dedent

import pytest

# Make `tools/` importable as a top-level package (mirrors how the
# existing test files in tools/sim/ resolve siblings).
TOOLS_DIR = Path(__file__).resolve().parent.parent
ROOT_DIR = TOOLS_DIR.parent
sys.path.insert(0, str(ROOT_DIR))

from tools import dep_graph  # noqa: E402


# ---------------------------------------------------------------------------
# Synthetic Pythia/ fixture
# ---------------------------------------------------------------------------


def _write_lean(path: Path, body: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(dedent(body).lstrip("\n"), encoding="utf-8")


@pytest.fixture
def synth_pythia(tmp_path: Path) -> Path:
    """A small Pythia/ tree with three tags and a known dep structure.

    Layout:
        Bio/Lemmas.lean      — base_lemma (stat_lemma), helper (stats_ineq)
        Bio/Theorem.lean     — top_theorem (stat_lemma), uses base_lemma + helper
        Other/Untagged.lean  — untagged_lemma (no attribute), should be ignored
        Mixed.lean           — multi_tag (stat_lemma + prob_simp), self_ref
    """
    root = tmp_path / "Pythia"
    _write_lean(root / "Bio" / "Lemmas.lean", """
        import Mathlib

        namespace Pythia

        @[stat_lemma]
        theorem base_lemma (a : Nat) : a + 0 = a := by
          rfl

        @[stats_ineq]
        theorem helper (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by
          omega

        end Pythia
    """)
    _write_lean(root / "Bio" / "Theorem.lean", """
        import Pythia.Bio.Lemmas

        namespace Pythia

        @[stat_lemma]
        theorem top_theorem (a b : Nat) : a + 0 ≤ b + 1 ∨ True := by
          right
          -- relies on base_lemma and helper for the actual proof
          have h1 := base_lemma a
          have h2 := helper a b
          trivial

        end Pythia
    """)
    _write_lean(root / "Other" / "Untagged.lean", """
        namespace Pythia

        theorem untagged_lemma (a : Nat) : a = a := rfl

        end Pythia
    """)
    _write_lean(root / "Mixed.lean", """
        namespace Pythia

        @[stat_lemma, prob_simp]
        theorem multi_tag (a : Nat) : a = a := by
          -- references base_lemma in body
          have := base_lemma a
          rfl

        @[prob_simp]
        theorem self_ref (a : Nat) : a = a := by
          -- mentions self_ref in a comment but comments are stripped
          rfl

        end Pythia
    """)
    return root


# ---------------------------------------------------------------------------
# Tests — parsing
# ---------------------------------------------------------------------------


def test_walk_pythia_finds_all_tagged(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    names = {t.name for t in theorems}
    assert "base_lemma" in names
    assert "helper" in names
    assert "top_theorem" in names
    assert "multi_tag" in names
    assert "self_ref" in names
    # Untagged lemma must not appear.
    assert "untagged_lemma" not in names


def test_parse_file_extracts_tags(synth_pythia: Path) -> None:
    theorems = dep_graph.parse_file(synth_pythia / "Mixed.lean")
    # multi_tag carries both stat_lemma and prob_simp.
    by_name = {t.name: t for t in theorems}
    assert "multi_tag" in by_name
    assert by_name["multi_tag"].tags == frozenset({"stat_lemma", "prob_simp"})
    assert by_name["self_ref"].tags == frozenset({"prob_simp"})


def test_strip_comments_removes_block_and_line() -> None:
    src = "theorem x := by\n  have := foo  -- comment foo\n/- block foo -/\n"
    out = dep_graph._strip_comments(src)
    # Both comments scrubbed; outside-comment `foo` survives.
    assert out.count("foo") == 1


def test_split_attr_list_handles_compound() -> None:
    parts = dep_graph._split_attr_list("stat_lemma, simp ↓, prob_simp")
    assert parts == ["stat_lemma", "simp", "prob_simp"]


# ---------------------------------------------------------------------------
# Tests — graph construction
# ---------------------------------------------------------------------------


def test_build_graph_edges_caller_to_callee(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    # top_theorem references base_lemma and helper.
    assert ("top_theorem", "base_lemma") in g.edges
    assert ("top_theorem", "helper") in g.edges
    # multi_tag references base_lemma.
    assert ("multi_tag", "base_lemma") in g.edges


def test_build_graph_no_self_edges(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    for a, b in g.edges:
        assert a != b, f"unexpected self-edge: {a}"


def test_filter_graph_subsets(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    only_bio = dep_graph.filter_graph(g, r"Bio/")
    # Mixed.lean theorems gone; Bio/* theorems retained.
    assert "base_lemma" in only_bio.nodes
    assert "top_theorem" in only_bio.nodes
    assert "multi_tag" not in only_bio.nodes
    # Edges with at least one endpoint outside the filter must be dropped.
    for a, b in only_bio.edges:
        assert a in only_bio.nodes
        assert b in only_bio.nodes


def test_filter_graph_by_name(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    only_top = dep_graph.filter_graph(g, r"^top_")
    assert only_top.nodes.keys() == {"top_theorem"}
    assert only_top.edges == set()


def test_max_depth_zero_is_noop(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    same = dep_graph.limit_depth(g, 0)
    assert set(same.nodes) == set(g.nodes)
    assert same.edges == g.edges


def test_max_depth_one_keeps_immediate_callees(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    shallow = dep_graph.limit_depth(g, 1)
    # top_theorem is a root; depth 1 should still reach base_lemma + helper.
    assert ("top_theorem", "base_lemma") in shallow.edges
    assert ("top_theorem", "helper") in shallow.edges


# ---------------------------------------------------------------------------
# Tests — emitters
# ---------------------------------------------------------------------------


def test_emit_mermaid_well_formed(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    out = dep_graph.emit_mermaid(g)
    assert out.startswith("```mermaid\n")
    assert "graph TD" in out
    assert out.rstrip().endswith("```")
    # Edge syntax `a --> b` must appear.
    assert re.search(r"^\s+\w+ --> \w+$", out, flags=re.MULTILINE)
    # Each node must have a style line for color coding.
    for name in g.nodes:
        assert f"style {name}" in out


def test_emit_dot_well_formed(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    out = dep_graph.emit_dot(g)
    assert out.startswith("digraph dep_graph {")
    assert out.rstrip().endswith("}")
    assert "rankdir=TD" in out
    # Every edge expressed as "a" -> "b";
    for a, b in g.edges:
        assert f'"{a}" -> "{b}";' in out


def test_emit_markdown_document_has_preamble(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    g = dep_graph.build_graph(theorems)
    out = dep_graph.emit_markdown_document(g)
    assert "Auto-generated by `tools/dep_graph.py`" in out
    assert "Do not hand-edit" in out
    assert "```mermaid" in out
    # Legend must mention every known tag.
    for tag in dep_graph.KNOWN_TAGS:
        assert f"@[{tag}]" in out


def test_primary_tag_prefers_known_order(synth_pythia: Path) -> None:
    theorems = dep_graph.walk_pythia(synth_pythia)
    by_name = {t.name: t for t in theorems}
    # multi_tag carries both stat_lemma and prob_simp; stat_lemma wins
    # because KNOWN_TAGS lists it first.
    assert dep_graph._primary_tag(by_name["multi_tag"]) == "stat_lemma"


# ---------------------------------------------------------------------------
# Tests — CLI integration
# ---------------------------------------------------------------------------


def test_cli_writes_output_file(synth_pythia: Path, tmp_path: Path) -> None:
    out_path = tmp_path / "out.md"
    rc = dep_graph.main([
        "--root", str(synth_pythia),
        "--output", str(out_path),
    ])
    assert rc == 0
    txt = out_path.read_text(encoding="utf-8")
    assert "graph TD" in txt
    # .md output should carry the documented preamble.
    assert "Auto-generated" in txt


def test_cli_format_dot(synth_pythia: Path, tmp_path: Path) -> None:
    out_path = tmp_path / "out.dot"
    rc = dep_graph.main([
        "--root", str(synth_pythia),
        "--format", "dot",
        "--output", str(out_path),
    ])
    assert rc == 0
    txt = out_path.read_text(encoding="utf-8")
    assert txt.startswith("digraph dep_graph {")


def test_cli_filter_subsets(synth_pythia: Path, tmp_path: Path) -> None:
    out_path = tmp_path / "out.md"
    rc = dep_graph.main([
        "--root", str(synth_pythia),
        "--filter", "Bio/",
        "--output", str(out_path),
    ])
    assert rc == 0
    txt = out_path.read_text(encoding="utf-8")
    assert "base_lemma" in txt
    # Mixed theorems should NOT survive a Bio/ filter.
    assert "multi_tag" not in txt


def test_cli_bad_root_returns_2(tmp_path: Path) -> None:
    rc = dep_graph.main(["--root", str(tmp_path / "nope")])
    assert rc == 2


def test_cli_subprocess_smoke(synth_pythia: Path) -> None:
    """End-to-end smoke through `python3 tools/dep_graph.py`."""
    script = ROOT_DIR / "tools" / "dep_graph.py"
    result = subprocess.run(
        [sys.executable, str(script), "--root", str(synth_pythia)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "```mermaid" in result.stdout
    assert "graph TD" in result.stdout
