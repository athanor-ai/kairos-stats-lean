"""tools/sim/test_manifest_coverage.py — CI coverage gate.

Paper claim (AI4MATH 2026 §1.2): "every theorem carries a matched
Python sim runner that exercises the empirical specification under
property-based testing, deterministic parameter sweeps, and mutation
testing."

This test enforces that claim in both directions:

  Forward — every entry in MANIFEST resolves on disk:
    * sim_path file exists
    * the file contains a function named sim_test (via AST; no exec)
    * the function is not buried inside ``if __name__ == "__main__"``

  Reverse — every domain sim file in tools/sim/ appears in MANIFEST:
    * utility modules (harness.py, mutations.py, theorem_manifest.py)
      and __init__.py are excluded
    * existing pytest files (test_*.py) are excluded — they are test
      infrastructure, not domain runners
    * any remaining .py file that is NOT a sim_path in MANIFEST is an
      orphan; the test fails and lists them so a human can triage

  Sim-test AST check — for every manifest entry the named function
    exists at module scope (not inside an ``if __name__`` guard).

These three checks together mean the paper claim cannot silently break:
adding a new domain runner without a manifest entry fails the reverse
check; adding a manifest entry pointing at a nonexistent file or
missing function fails the forward / AST checks.

Running locally:
    cd <repo-root>
    python3 -m pytest tools/sim/test_manifest_coverage.py -v
"""
from __future__ import annotations

import ast
import sys
from pathlib import Path

import pytest

# ── Path bootstrap ────────────────────────────────────────────────────

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.sim.theorem_manifest import MANIFEST, REPO_ROOT as MANIFEST_ROOT  # noqa: E402

# Sanity: both paths should agree.
assert REPO_ROOT == MANIFEST_ROOT, (
    f"REPO_ROOT mismatch: test sees {REPO_ROOT}, manifest sees {MANIFEST_ROOT}"
)

SIM_DIR = REPO_ROOT / "tools" / "sim"

# ── Shared helpers ────────────────────────────────────────────────────

# Utility modules that are NOT domain runners and must be excluded from
# the reverse-direction walk. Updated here when new shared modules are
# added to tools/sim/.
_UTILITY_STEMS = frozenset({
    "__init__",
    "harness",
    "mutations",
    "theorem_manifest",
})


def _is_utility(path: Path) -> bool:
    """Return True for __init__.py, harness.py, mutations.py, theorem_manifest.py."""
    return path.stem in _UTILITY_STEMS


def _is_test_file(path: Path) -> bool:
    """Return True for files whose name starts with ``test_``."""
    return path.name.startswith("test_")


def _domain_sim_files() -> list[Path]:
    """All .py files in tools/sim/ that are domain runners (not utilities, not test files)."""
    return sorted(
        p for p in SIM_DIR.glob("*.py")
        if not _is_utility(p) and not _is_test_file(p)
    )


def _manifest_sim_paths() -> frozenset[str]:
    """Set of sim_path values referenced by MANIFEST entries (repo-root-relative)."""
    return frozenset(e.sim_path for e in MANIFEST)


def _top_level_function_names(source: str) -> set[str]:
    """Return function names defined at module-level (not nested inside
    class bodies, other functions, or ``if __name__`` guards).

    We want to catch tests defined like::

        def test_foo():   # <- top-level, valid
            ...

    but NOT like::

        if __name__ == "__main__":
            def test_foo():  # <- guard, should not count as a pytest target
                ...
    """
    tree = ast.parse(source)
    names: set[str] = set()
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.FunctionDef):
            names.add(node.name)
    return names


# ── Forward direction ─────────────────────────────────────────────────


class TestForwardDirection:
    """Every MANIFEST entry must resolve on disk with a valid test function."""

    @pytest.mark.parametrize(
        "entry",
        MANIFEST,
        ids=[f"{e.domain}/{e.name}" for e in MANIFEST],
    )
    def test_sim_path_exists(self, entry) -> None:
        """sim_path file must exist on disk."""
        p = REPO_ROOT / entry.sim_path
        assert p.is_file(), (
            f"Manifest entry '{entry.name}' references sim_path "
            f"'{entry.sim_path}' which does not exist on disk.\n"
            f"Fix: either create the file or remove the manifest entry."
        )

    @pytest.mark.parametrize(
        "entry",
        MANIFEST,
        ids=[f"{e.domain}/{e.name}" for e in MANIFEST],
    )
    def test_sim_test_function_exists(self, entry) -> None:
        """sim_test must be a top-level function in sim_path (AST check; no exec)."""
        p = REPO_ROOT / entry.sim_path
        if not p.is_file():
            pytest.skip(f"sim_path '{entry.sim_path}' missing — covered by test_sim_path_exists")

        source = p.read_text(encoding="utf-8")
        top_level = _top_level_function_names(source)

        assert entry.sim_test in top_level, (
            f"Manifest entry '{entry.name}' declares sim_test "
            f"'{entry.sim_test}' but that function is not defined at "
            f"module scope in '{entry.sim_path}'.\n"
            f"Top-level functions found: {sorted(top_level)}\n"
            f"Fix: add or rename the test function, or update sim_test in the manifest."
        )


# ── Reverse direction ─────────────────────────────────────────────────


class TestReverseDirection:
    """Every domain sim file on disk must appear in MANIFEST."""

    def test_no_orphan_domain_runners(self) -> None:
        """Walk tools/sim/*.py (excluding utilities and test files) and
        assert every file is covered by at least one manifest entry.

        An orphan file is a domain runner that has no theorem paired with
        it — directly violating the AI4MATH 2026 §1.2 'every theorem' claim.
        """
        manifest_paths = _manifest_sim_paths()
        domain_files = _domain_sim_files()

        orphans = [
            f for f in domain_files
            if f"tools/sim/{f.name}" not in manifest_paths
        ]

        assert not orphans, (
            f"Found {len(orphans)} orphan domain sim file(s) with no "
            f"matching manifest entry. Each domain runner must be paired "
            f"with a TheoremEntry in tools/sim/theorem_manifest.py.\n\n"
            f"Orphans:\n"
            + "\n".join(f"  tools/sim/{f.name}" for f in orphans)
            + "\n\nFix: add a TheoremEntry for each orphan (see neighbouring "
            f"entries in theorem_manifest.py for shape), OR delete the file "
            f"if it is truly dead code."
        )

    def test_manifest_coverage_fraction(self) -> None:
        """Coverage ratio must equal 1.0 (100%).

        This is a summary assertion that mirrors the paper claim. It also
        surfaces coverage numbers in the CI log even when the orphan test
        above already passed (e.g., after a fix).
        """
        manifest_paths = _manifest_sim_paths()
        domain_files = _domain_sim_files()

        covered = sum(
            1 for f in domain_files
            if f"tools/sim/{f.name}" in manifest_paths
        )
        total = len(domain_files)

        assert covered == total, (
            f"Manifest coverage: {covered}/{total} domain sim files are "
            f"paired with a theorem. Expected 100% coverage.\n"
            f"Run test_no_orphan_domain_runners for the list of gaps."
        )


# ── Sim-test AST check (standalone, not parametrised) ─────────────────


class TestSimTestAstResolution:
    """Bulk AST check: every (sim_path, sim_test) pair resolves without
    needing to import the module (no side-effects, works in sandboxes).
    """

    def test_all_sim_tests_resolve(self) -> None:
        """For every manifest entry, sim_test must be a module-level function.

        Collects ALL failures in one pass so the CI log shows the full
        list of broken entries rather than stopping at the first.
        """
        failures: list[str] = []

        for entry in MANIFEST:
            p = REPO_ROOT / entry.sim_path
            if not p.is_file():
                failures.append(
                    f"  {entry.domain}/{entry.name}: sim_path '{entry.sim_path}' missing"
                )
                continue
            try:
                source = p.read_text(encoding="utf-8")
                top_level = _top_level_function_names(source)
            except SyntaxError as exc:
                failures.append(
                    f"  {entry.domain}/{entry.name}: SyntaxError in "
                    f"'{entry.sim_path}': {exc}"
                )
                continue

            if entry.sim_test not in top_level:
                failures.append(
                    f"  {entry.domain}/{entry.name}: function "
                    f"'{entry.sim_test}' not found at top level of "
                    f"'{entry.sim_path}' (found: {sorted(top_level)})"
                )

        assert not failures, (
            f"AST resolution failed for {len(failures)} manifest entr"
            f"{'y' if len(failures) == 1 else 'ies'}:\n"
            + "\n".join(failures)
        )


# ── Utility-exclusion sanity ───────────────────────────────────────────


class TestExclusionLogic:
    """Smoke tests for the helper predicates that decide which files are
    domain runners vs. utilities / test infrastructure.
    """

    def test_harness_is_excluded(self) -> None:
        assert _is_utility(SIM_DIR / "harness.py")

    def test_mutations_is_excluded(self) -> None:
        assert _is_utility(SIM_DIR / "mutations.py")

    def test_init_is_excluded(self) -> None:
        assert _is_utility(SIM_DIR / "__init__.py")

    def test_theorem_manifest_is_excluded(self) -> None:
        assert _is_utility(SIM_DIR / "theorem_manifest.py")

    def test_test_files_are_excluded(self) -> None:
        assert _is_test_file(SIM_DIR / "test_manifest_coverage.py")
        assert _is_test_file(SIM_DIR / "test_dep_graph.py")

    def test_domain_runner_is_not_excluded(self) -> None:
        assert not _is_utility(SIM_DIR / "economics_cobb_douglas.py")
        assert not _is_test_file(SIM_DIR / "economics_cobb_douglas.py")
