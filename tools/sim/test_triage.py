"""tools/sim/test_triage.py — CI gates for the orphan-module triage.

The triage classifies every ``Pythia/*.lean`` module into Tier-A
(user-facing applied math), Tier-B (statistics-spine
infrastructure), or Tier-C (pure Lean structural). The
classification drives the v2 sim-runner backfill (ATH-792).

Audit (2026-04-27) found that the original triage agent
hallucinated 9 Tier-A ``theorem_names`` that did not exist in
their declared source files. Those were fixed in the same PR
that added these tests. The tests below prevent the regression
from recurring.

What's enforced:

  1. JSON validates against the schema.
  2. Triage covers every ``Pythia/**/*.lean`` (excluding
     ``*Test.lean``); no missing files, no stale entries
     pointing at deleted files.
  3. Per-tier counts are within reasonable bounds — caught
     accidental tier mass-drift, e.g., everything getting
     classified Tier-C and the backfill becoming a no-op.
  4. **Every Tier-A entry's declared theorem_names actually
     exist in the source file** — this is the test that catches
     the hallucination bug. Uses ``tools.sim.lean_decls``
     (line-based parser, no regex).

What's NOT enforced (out of scope for this gate):
  - Tier-A vs Tier-B classification correctness — that's a
    judgement call, validated by review.
  - Symmetry tag accuracy — same as above.
  - Whether Tier-A modules deserve their classification.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

import jsonschema
import pytest

from tools.sim.lean_decls import top_level_decls_in_file

REPO_ROOT = Path(__file__).resolve().parents[2]
TRIAGE_JSON = REPO_ROOT / "tools" / "sim" / "triage.json"
TRIAGE_SCHEMA = REPO_ROOT / "tools" / "sim" / "triage_schema.json"


@pytest.fixture(scope="module")
def triage_data() -> dict:
    return json.loads(TRIAGE_JSON.read_text(encoding="utf-8"))


@pytest.fixture(scope="module")
def triage_schema_data() -> dict:
    return json.loads(TRIAGE_SCHEMA.read_text(encoding="utf-8"))


# ── Schema validation ───────────────────────────────────────────────


class TestSchemaValidation:
    def test_triage_validates_against_schema(self, triage_data, triage_schema_data) -> None:
        jsonschema.validate(instance=triage_data, schema=triage_schema_data)


# ── Completeness ────────────────────────────────────────────────────


class TestCoverageCompleteness:
    """Every Pythia/**/*.lean (excluding *Test.lean) must appear in
    the triage. No stale entries pointing at deleted files."""

    def _disk_lean_files(self) -> set[str]:
        out: set[str] = set()
        for p in (REPO_ROOT / "Pythia").rglob("*.lean"):
            if p.name.endswith("Test.lean"):
                continue
            out.add(str(p.relative_to(REPO_ROOT)))
        return out

    def test_no_lean_files_missing_from_triage(self, triage_data) -> None:
        disk = self._disk_lean_files()
        missing = sorted(disk - triage_data.keys())
        assert not missing, (
            f"{len(missing)} Lean file(s) not classified in triage:\n"
            + "\n".join(f"  - {p}" for p in missing[:20])
        )

    def test_no_stale_triage_entries(self, triage_data) -> None:
        disk = self._disk_lean_files()
        stale = sorted(set(triage_data.keys()) - disk)
        assert not stale, (
            f"{len(stale)} triage entry(ies) point at deleted Lean files:\n"
            + "\n".join(f"  - {p}" for p in stale[:20])
        )


# ── Tier-balance sanity ─────────────────────────────────────────────


class TestTierBalance:
    """Catch accidental mass-drift like 'everything got classified
    Tier-C' or 'no Tier-A modules at all'. Bounds are intentionally
    loose; this is a smoke test, not a prescription."""

    def _tier_counts(self, triage_data: dict) -> Counter:
        return Counter(v["tier"] for v in triage_data.values())

    def test_tiers_use_only_abc(self, triage_data) -> None:
        tiers = set(self._tier_counts(triage_data).keys())
        assert tiers <= {"A", "B", "C"}, f"unexpected tier values: {tiers}"

    def test_tier_a_floor(self, triage_data) -> None:
        """The backfill needs at least 30 Tier-A modules — otherwise
        the cross-domain corpus claim ('30+ theorems') breaks."""
        n = self._tier_counts(triage_data).get("A", 0)
        assert n >= 30, f"Tier-A count {n} < 30 floor"

    def test_no_tier_dominates_pathologically(self, triage_data) -> None:
        """No single tier should be >85% of all modules.

        If 90%+ are Tier-C, the triage is mass-misclassified
        toward 'no sim needed' and the backfill becomes a no-op.
        If 90%+ are Tier-A, every module needs a sim and the
        shared spine-sim design is wasted."""
        counts = self._tier_counts(triage_data)
        total = sum(counts.values())
        for tier, n in counts.items():
            assert n / total <= 0.85, (
                f"Tier-{tier} = {n}/{total} ({n/total:.0%}); "
                "exceeds 85% pathological threshold."
            )


# ── Tier-A theorem_names exist in source ────────────────────────────


class TestTierATheoremNamesExist:
    """REGRESSION GATE for the 2026-04-27 audit finding.

    Triage agent hallucinated 9 theorem names that didn't exist in
    their declared source files (e.g., declared
    ``matrix_bernstein`` while the source had
    ``matrixBernstein_self_adjoint``). Those were fixed in the
    same PR. This test prevents future hallucinations.

    Approach: parse the Lean source via the line-based
    ``tools.sim.lean_decls`` parser (no regex per the
    feedback_no_regex_use_real_parsers.md rule), collect every
    top-level declaration's unqualified identifier, assert every
    Tier-A entry's ``theorem_names`` (after stripping namespace
    prefix) is in that set.
    """

    def test_every_tier_a_theorem_name_exists_in_source(
        self, triage_data
    ) -> None:
        mismatches: list[tuple[str, str, list[str]]] = []
        for path, entry in triage_data.items():
            if entry.get("tier") != "A":
                continue
            src_decls = top_level_decls_in_file(REPO_ROOT / path)
            for declared in entry.get("theorem_names", []):
                unqual = declared.split(".")[-1]
                if unqual not in src_decls:
                    mismatches.append(
                        (path, declared, sorted(src_decls)[:8])
                    )
        if mismatches:
            lines = [
                f"{len(mismatches)} hallucinated theorem name(s) in triage.json:"
            ]
            for path, name, source_sample in mismatches:
                lines.append(f"  {path}:")
                lines.append(f"    declared: {name!r}")
                lines.append(f"    source actually has: {source_sample}")
            lines.append("")
            lines.append(
                "Fix: update the theorem_names entry in triage.json to "
                "match the actual top-level declaration name(s) in the "
                "source file. Use tools.sim.lean_decls.top_level_decls_in_file "
                "to enumerate them."
            )
            pytest.fail("\n".join(lines))


# ── lean_decls parser unit tests ─────────────────────────────────────


class TestLeanDeclsParser:
    """Unit tests for :func:`top_level_decls`. Pinning behaviour on
    synthetic inputs so the regression gate above is trustable."""

    def test_extracts_theorem(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = "theorem foo (x : Nat) : x = x := rfl\n"
        assert top_level_decls(src) == {"foo"}

    def test_extracts_lemma(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = "lemma bar : True := trivial\n"
        assert top_level_decls(src) == {"bar"}

    def test_extracts_def(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = "def baz (n : Nat) : Nat := n + 1\n"
        assert top_level_decls(src) == {"baz"}

    def test_strips_attribute_prefix(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = "@[simp] theorem foo : True := trivial\n"
        assert "foo" in top_level_decls(src)

    def test_strips_complex_attribute(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = "@[stat_lemma, simp] lemma bar : True := trivial\n"
        assert "bar" in top_level_decls(src)

    def test_skips_indented_inner_defs(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = (
            "theorem outer : True := by\n"
            "  have inner_helper : True := trivial\n"
            "  exact inner_helper\n"
        )
        # Only `outer` is top-level.
        assert top_level_decls(src) == {"outer"}

    def test_skips_comments(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = (
            "-- theorem fake : True := trivial\n"
            "/- theorem also_fake : True := trivial -/\n"
            "theorem real : True := trivial\n"
        )
        assert top_level_decls(src) == {"real"}

    def test_handles_namespace_qualified_decls(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        # Lean 4 allows `theorem Foo.bar : ...` even outside namespace blocks.
        src = "theorem Foo.bar : True := trivial\n"
        # We return the unqualified rightmost segment.
        assert top_level_decls(src) == {"bar"}

    def test_handles_multiple_decls(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = (
            "theorem first : True := trivial\n"
            "lemma second : True := trivial\n"
            "def third : Nat := 0\n"
        )
        assert top_level_decls(src) == {"first", "second", "third"}

    def test_handles_noncomputable_def(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = "noncomputable def heavy : ℝ := sorry\n"
        assert top_level_decls(src) == {"heavy"}

    def test_returns_empty_for_empty_source(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        assert top_level_decls("") == set()

    def test_ignores_lines_without_keywords(self) -> None:
        from tools.sim.lean_decls import top_level_decls
        src = (
            "namespace Foo\n"
            "open Bar\n"
            "variable (x : Nat)\n"
        )
        assert top_level_decls(src) == set()
