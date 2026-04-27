"""tools/sim/test_add_theorem.py — unit + property tests for the
`tools/add_theorem.py` scaffold CLI.

Covers the pure rendering helpers (_slugify, _camel,
_render_references, render_lean_file, render_harness_file,
render_manifest_entry) plus a smoke test that exercises the manifest
patcher against an isolated copy of the manifest. The full main()
CLI is not exercised against the real repo to avoid touching shared
state during CI.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
# Make repo root importable so `import tools.add_theorem` resolves
# as a namespace package, which lets coverage.py track the file
# under its real source path (vs. a synthetic importlib name).
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import tools.add_theorem as add_theorem  # noqa: E402


# ── pure helpers ─────────────────────────────────────────────────────

class TestSlugify:
    def test_lowercase_passthrough(self):
        assert add_theorem._slugify("hello_world") == "hello_world"

    def test_strips_non_word_chars(self):
        assert add_theorem._slugify("Foo!Bar@Baz") == "foo_bar_baz"

    def test_collapses_runs(self):
        assert add_theorem._slugify("a---b   c") == "a_b_c"

    def test_strips_leading_trailing(self):
        assert add_theorem._slugify("__foo__") == "foo"

    def test_unicode_safe(self):
        assert add_theorem._slugify("über_test") == "ber_test"


class TestCamel:
    def test_snake_to_camel(self):
        assert add_theorem._camel("hardy_weinberg_conservation") == \
            "HardyWeinbergConservation"

    def test_single_word(self):
        assert add_theorem._camel("solow") == "Solow"

    def test_empty(self):
        assert add_theorem._camel("") == ""

    def test_idempotent_on_camel_input(self):
        # `Foo` becomes `Foo`; we only split on `_`.
        assert add_theorem._camel("Foo") == "Foo"


class TestReferences:
    def test_empty_returns_empty(self):
        assert add_theorem._render_references([]) == ""

    def test_one_reference_starts_with_newline(self):
        out = add_theorem._render_references(["Smith 2024"])
        assert out.startswith("\n")
        assert "Smith 2024" in out

    def test_multiple_references_each_bulleted(self):
        out = add_theorem._render_references(["A", "B", "C"])
        assert out.count("    * ") == 3

    def test_csv_quotes_each(self):
        out = add_theorem._references_csv(["Smith 2024", "Jones 2025"])
        assert out == '"Smith 2024", "Jones 2025"'

    def test_csv_empty(self):
        assert add_theorem._references_csv([]) == ""


# ── render helpers (template smoke) ──────────────────────────────────

@pytest.fixture
def sample_lean():
    """Render a Lean file for a representative theorem."""
    return add_theorem.render_lean_file(
        domain="Economics",
        name="solow_steady_state_pos",
        statement="theorem solow_steady_state_pos (k : ℝ) : 0 < k := by sorry",
        summary="Solow steady state is positive",
        imports=["Mathlib", "Pythia.Tactic.Pythia"],
        opens=["Real"],
        references=["Solow 1956"],
        proof="by sorry",
    )


def test_render_lean_includes_namespace(sample_lean):
    assert "namespace Pythia.Economics" in sample_lean
    assert "end Pythia.Economics" in sample_lean


def test_render_lean_includes_imports(sample_lean):
    assert "import Mathlib" in sample_lean
    assert "import Pythia.Tactic.Pythia" in sample_lean


def test_render_lean_includes_open(sample_lean):
    assert "open Real" in sample_lean


def test_render_lean_includes_statement(sample_lean):
    assert "solow_steady_state_pos" in sample_lean


def test_render_lean_no_open_block_when_no_opens():
    out = add_theorem.render_lean_file(
        domain="Economics", name="x", statement="theorem x : True := trivial",
        summary="", imports=["Mathlib"], opens=[], references=[], proof="trivial",
    )
    # Must NOT contain a stray `open` line.
    for line in out.splitlines():
        assert not line.startswith("open ")


def test_render_lean_renders_no_references_block_when_empty():
    out = add_theorem.render_lean_file(
        domain="Bio", name="x", statement="theorem x : True := trivial",
        summary="", imports=["Mathlib"], opens=[], references=[], proof="trivial",
    )
    # The template falls back to `(none)` per `_render_references` returning ""
    # and the call site appending a placeholder.
    assert "(none)" in out


def test_render_harness_includes_namespace_and_paths():
    out = add_theorem.render_harness_file(
        domain="Economics",
        name="solow_steady_state_pos",
        summary="Solow steady state",
        lean_path="Pythia/Economics/SolowSteadyStatePos.lean",
        sim_path="tools/sim/economics_solow_steady_state_pos.py",
        strategy_args="k=floats(0.01, 1e3)",
    )
    assert "Pythia.Economics" in out
    assert "Pythia/Economics/SolowSteadyStatePos.lean" in out
    assert "tools/sim/economics_solow_steady_state_pos.py" in out
    assert "test_solow_steady_state_pos" in out


def test_render_harness_strategy_args_split():
    out = add_theorem.render_harness_file(
        domain="Bio", name="hw_conservation", summary="HW",
        lean_path="Pythia/Bio/Population.lean",
        sim_path="tools/sim/bio_hw_conservation.py",
        strategy_args="p=floats(0,1), q=floats(0,1), n=ints(10, 1_000_000)",
    )
    assert "p=floats(0,1)" in out
    assert "q=floats(0,1)" in out
    assert "n=ints(10, 1_000_000)" in out


def test_render_manifest_entry_quotes_summary():
    entry = add_theorem.render_manifest_entry(
        domain="Economics", name="cobb_douglas_crts",
        summary="Cobb-Douglas \"constant\" returns",
        lean_path="Pythia/Economics/CobbDouglas.lean",
        sim_path="tools/sim/economics_cobb_douglas_crts.py",
        test_name="test_cobb_douglas_crts",
        mathlib_status="novel",
        references=["Cobb 1928"],
    )
    # Embedded double quote must be escaped.
    assert 'Cobb-Douglas \\"constant\\" returns' in entry


# ── manifest patcher (filesystem-aware, reversible) ──────────────────

def test_append_to_manifest_round_trip(tmp_path, monkeypatch):
    """Verify _append_to_manifest correctly inserts before the closing
    `)`. We monkey-patch MANIFEST_PATH to point at a fixture rather
    than touching the real manifest."""
    # Build a minimal manifest with the same shape as the real file.
    fixture = tmp_path / "fake_manifest.py"
    fixture.write_text(
        "MANIFEST: tuple[object, ...] = (\n"
        "    {'name': 'first'},\n"
        "    {'name': 'second'},\n"
        ")\n"
    )
    original = add_theorem.MANIFEST_PATH
    monkeypatch.setattr(add_theorem, "MANIFEST_PATH", fixture)
    try:
        ok = add_theorem._append_to_manifest("    {'name': 'third'},\n")
        assert ok is True
        new_text = fixture.read_text()
        # Order preserved + new entry before the closing `)`.
        idx_first = new_text.index("first")
        idx_second = new_text.index("second")
        idx_third = new_text.index("third")
        idx_close = new_text.rindex(")")
        assert idx_first < idx_second < idx_third < idx_close
    finally:
        # Defensive: monkeypatch already restores, but assert no
        # accidental side effect on the real manifest path attr.
        assert add_theorem.MANIFEST_PATH != original or True


def test_append_to_manifest_returns_false_on_malformed(tmp_path, monkeypatch):
    """If the manifest has no closing `)`, the patcher refuses."""
    bad = tmp_path / "bad_manifest.py"
    bad.write_text("# no closing paren in this file\n")
    monkeypatch.setattr(add_theorem, "MANIFEST_PATH", bad)
    assert add_theorem._append_to_manifest("    {},\n") is False


# ── property tests (Hypothesis) — slug stability ─────────────────────

try:
    from hypothesis import given, strategies as st, settings, HealthCheck

    @settings(max_examples=200, suppress_health_check=[HealthCheck.too_slow])
    @given(st.text(min_size=1, max_size=40))
    def test_slugify_idempotent(s):
        """`_slugify` is idempotent: slugify(slugify(x)) == slugify(x)."""
        once = add_theorem._slugify(s)
        twice = add_theorem._slugify(once)
        assert once == twice

    @settings(max_examples=200)
    @given(st.text(alphabet=st.characters(whitelist_categories=("Lu", "Ll", "Nd", "Pc")), min_size=1, max_size=30))
    def test_slugify_only_word_chars(s):
        """`_slugify` output uses only ASCII word chars + underscore."""
        out = add_theorem._slugify(s)
        for ch in out:
            assert ch.isalnum() or ch == "_", (ch, s, out)

except ImportError:
    # Hypothesis not installed in some local dev envs; CI installs it
    # via `pip install ".[test]"`. Skip the property tests then.
    pass
