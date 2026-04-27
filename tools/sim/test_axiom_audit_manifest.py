"""tools/sim/test_axiom_audit_manifest.py — schema + helper unit tests
for the axiom-audit coverage manifest.

These tests do NOT invoke lake. They validate two things:

  1. The manifest itself (:data:`EXPECTED_AUDITED_THEOREMS`) is
     well-formed: non-empty, no duplicates, all strings, no
     surprising entries (whitespace, etc.).

  2. The :func:`find_missing` helper that the CI script uses
     correctly reports missing theorems on synthetic lake-output
     fixtures.

Acting on the actual lake output is the CI script's job
(``check_axiom_audit.py``); these unit tests pin its behaviour
without requiring lake to be on the test machine.
"""
from __future__ import annotations

from tools.sim.axiom_audit_manifest import EXPECTED_AUDITED_THEOREMS
from tools.sim.check_axiom_audit import find_missing


# ── Manifest schema ──────────────────────────────────────────────────


class TestManifestStructure:
    def test_manifest_is_non_empty(self) -> None:
        assert len(EXPECTED_AUDITED_THEOREMS) > 0

    def test_manifest_floor_count(self) -> None:
        """Coverage floor: bump this when adding theorems, never lower it.

        Catches accidental deletion of entries during refactor.
        """
        floor = 51  # Audit count at 2026-04-27.
        assert len(EXPECTED_AUDITED_THEOREMS) >= floor, (
            f"Manifest shrank: {len(EXPECTED_AUDITED_THEOREMS)} entries < floor {floor}. "
            "If this is intentional (theorem removed from library), "
            "lower the floor in the same PR with a note."
        )

    def test_manifest_entries_are_strings(self) -> None:
        for entry in EXPECTED_AUDITED_THEOREMS:
            assert isinstance(entry, str), (
                f"manifest entry not a str: {entry!r} ({type(entry).__name__})"
            )

    def test_manifest_entries_are_non_empty_and_trimmed(self) -> None:
        for entry in EXPECTED_AUDITED_THEOREMS:
            assert entry, "manifest contains empty string"
            assert entry == entry.strip(), (
                f"manifest entry has surrounding whitespace: {entry!r}"
            )

    def test_manifest_entries_have_no_internal_whitespace(self) -> None:
        for entry in EXPECTED_AUDITED_THEOREMS:
            assert " " not in entry and "\t" not in entry and "\n" not in entry, (
                f"manifest entry has internal whitespace: {entry!r}"
            )

    def test_manifest_includes_full_ville_family(self) -> None:
        """Paper §3 (anytime-valid) cites all four; ATH-781 resolved
        the namespace collision so all four can co-load. This test
        pins that resolved state."""
        ville = {
            "ville_supermartingale",
            "ville_supermartingale_unit_initial",
            "ville_bound_pos",
            "ville_supermartingale_finite",
        }
        missing = ville - EXPECTED_AUDITED_THEOREMS
        assert not missing, f"Ville family missing: {sorted(missing)}"


# ── find_missing helper ──────────────────────────────────────────────


class TestFindMissingHelper:
    """The helper compares each expected theorem against substrings
    of lake's emitted output. These tests pin behaviour on
    synthetic fixtures so the CI script is trustworthy."""

    _SYNTHETIC_OUTPUT_ALL_PRESENT = (
        "'foo' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'bar' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        "'baz' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    )

    def test_returns_empty_when_all_present(self) -> None:
        expected = frozenset({"foo", "bar", "baz"})
        missing = find_missing(self._SYNTHETIC_OUTPUT_ALL_PRESENT, expected)
        assert missing == []

    def test_lists_each_missing_entry(self) -> None:
        expected = frozenset({"foo", "qux", "quux"})
        missing = find_missing(self._SYNTHETIC_OUTPUT_ALL_PRESENT, expected)
        assert sorted(missing) == ["quux", "qux"]

    def test_returns_all_when_output_empty(self) -> None:
        expected = frozenset({"foo", "bar"})
        missing = find_missing("", expected)
        assert sorted(missing) == ["bar", "foo"]

    def test_substring_match_on_namespaced_decl(self) -> None:
        """A namespaced declaration like
        ``Pythia.InfoTheory.klDiv_bind_le_klDiv`` is matched as
        a substring; partial namespace matches are NOT enough."""
        output = (
            "'Pythia.InfoTheory.klDiv_bind_le_klDiv' depends on axioms: ...\n"
        )
        expected = frozenset({"Pythia.InfoTheory.klDiv_bind_le_klDiv"})
        assert find_missing(output, expected) == []

    def test_partial_namespace_does_not_match(self) -> None:
        """Output contains parent namespace but not the full decl name.
        Ensures we don't false-pass on substring-of-substring."""
        output = "'Pythia.InfoTheory' depends on axioms: ...\n"
        expected = frozenset({"Pythia.InfoTheory.klDiv_bind_le_klDiv"})
        assert find_missing(output, expected) == ["Pythia.InfoTheory.klDiv_bind_le_klDiv"]

    def test_returns_sorted_for_determinism(self) -> None:
        """The CI script prints the missing list; sorted output makes
        log diffs stable across runs."""
        expected = frozenset({"zeta", "alpha", "kappa", "beta"})
        missing = find_missing("", expected)
        assert missing == sorted(missing)

    def test_handles_real_decl_with_underscores_and_dots(self) -> None:
        output = (
            "'ville_supermartingale' depends on axioms: [propext, ...]\n"
            "'Pythia.Risk.CoherentMeasures.adeh_attained' depends on axioms: ...\n"
        )
        expected = frozenset({
            "ville_supermartingale",
            "Pythia.Risk.CoherentMeasures.adeh_attained",
        })
        assert find_missing(output, expected) == []
