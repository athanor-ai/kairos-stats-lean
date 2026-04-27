"""tools.sim.theorem_manifest — unit tests.

Verifies the manifest's invariants:

* every (lean_path, sim_path) actually exists on disk
* names are unique
* domains use known values
* mathlib_status is one of {'novel', 'retag', 'extension'}
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path

import pytest

from tools.sim.theorem_manifest import (
    MANIFEST,
    REPO_ROOT,
    TheoremEntry,
    assert_files_exist,
    by_domain,
    by_name,
    domains,
    pytest_args,
)


VALID_DOMAINS = {
    "economics", "chemistry", "biology", "engineering",
    "mechanical", "control", "or", "mathlib_tags",
}

VALID_MATHLIB_STATUS = {"novel", "retag", "extension"}


class TestManifestInvariants:

    def test_manifest_nonempty(self):
        assert len(MANIFEST) > 0, "manifest must list shipped theorems"

    def test_names_unique(self):
        names = [e.name for e in MANIFEST]
        counts = Counter(names)
        dupes = [n for n, c in counts.items() if c > 1]
        assert not dupes, f"duplicate theorem names in manifest: {dupes}"

    def test_lean_theorem_unique_or_intentional(self):
        # Two manifest entries CAN share the same Lean theorem if the
        # second is a retag pointing at a third-party (mathlib) name.
        # We assert pythia-owned names are unique.
        own = [e.lean_theorem for e in MANIFEST if e.lean_theorem.startswith("Pythia.")]
        counts = Counter(own)
        dupes = [n for n, c in counts.items() if c > 1]
        assert not dupes, f"duplicate Pythia-namespaced theorems: {dupes}"

    def test_all_domains_are_valid(self):
        for e in MANIFEST:
            assert e.domain in VALID_DOMAINS, (
                f"unknown domain {e.domain!r} on entry {e.name!r}; "
                f"valid: {sorted(VALID_DOMAINS)}"
            )

    def test_all_mathlib_status_are_valid(self):
        for e in MANIFEST:
            assert e.mathlib_status in VALID_MATHLIB_STATUS, (
                f"unknown mathlib_status {e.mathlib_status!r} on "
                f"{e.name!r}; valid: {sorted(VALID_MATHLIB_STATUS)}"
            )

    def test_files_exist(self):
        missing = assert_files_exist()
        assert not missing, f"manifest references missing files: {missing}"


class TestQueries:

    def test_by_domain_filters(self):
        econ = by_domain("economics")
        assert len(econ) >= 5  # at least cobb-douglas + crra + capm + call + walras
        for e in econ:
            assert e.domain == "economics"

    def test_by_name_returns_match(self):
        e = by_name("cobb_douglas_crts")
        assert e is not None
        assert e.lean_path == "Pythia/Economics/CobbDouglas.lean"

    def test_by_name_returns_none_for_unknown(self):
        assert by_name("nonexistent_theorem_xyz") is None

    def test_domains_are_listed(self):
        ds = domains()
        # Every domain in MANIFEST shows up exactly once.
        for e in MANIFEST:
            assert e.domain in ds

    def test_pytest_args_format(self):
        args = pytest_args()
        assert len(args) == len(MANIFEST)
        for arg in args:
            assert "::" in arg, f"expected pytest path::test format, got {arg!r}"
            sim_path, _, test_name = arg.partition("::")
            assert sim_path.startswith("tools/sim/")
            assert test_name.startswith("test_")
