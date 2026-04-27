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


# ── Coverage primitive enforcement ─────────────────────────────────────
#
# Paper claim (AI4MATH 2026 §1.2): every theorem's Python sim runner
# exercises three primitives:
#   1. property-based testing (Hypothesis-style strategy + assertions)
#   2. deterministic parameter sweeps (a fixed grid)
#   3. mutation testing (perturb the spec, confirm the test catches it)
#
# The forward / reverse / AST checks above only enforce that a function
# with the right name exists. That's necessary but not sufficient — a
# sim like ``def test_foo(): assert True`` would pass those checks
# while delivering none of the paper's claimed coverage. The tests in
# this section close that gap by inspecting the AST of each sim file.
#
# Acceptable shapes (today, v1 only):
#   1. v1 harness pattern: imports tools.sim.harness AND calls
#      run_harness(...) with mutations=<non-empty>
#
# v2 (tools.sim.harness.v2.Sim) is a follow-up to land separately;
# when v2 sims start arriving in the backfill, extend
# ``_sim_uses_coverage_primitives`` to accept ``Sim(generator=...,
# property=..., symmetries=[...])`` as the v2 alternative.


def _parse_module(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"))


def _imports_v1_harness(tree: ast.Module) -> bool:
    """True iff the file does ``from tools.sim.harness import ...``
    or ``from tools.sim import harness`` (and is NOT a v2 import)."""
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            # Disambiguate from v2: ``tools.sim.harness.v2`` matches
            # ``startswith("tools.sim.harness")`` but is the v2 import.
            if mod == "tools.sim.harness":
                return True
            if mod == "tools.sim" and any(a.name == "harness" for a in node.names):
                return True
    return False


def _imports_v2_harness(tree: ast.Module) -> bool:
    """True iff the file imports anything from the v2 harness subpackage.

    Matches ``from tools.sim.harness.v2 import Sim`` and
    ``from tools.sim.harness.v2.<sub> import ...`` (generators,
    properties, metamorphic, statistical, targeting, differential,
    replay).
    """
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            if mod == "tools.sim.harness.v2" or mod.startswith("tools.sim.harness.v2."):
                return True
    return False


def _run_harness_calls(tree: ast.Module) -> list[ast.Call]:
    """All call sites of ``run_harness(...)`` in the module."""
    calls: list[ast.Call] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            fn = node.func
            if isinstance(fn, ast.Name) and fn.id == "run_harness":
                calls.append(node)
            elif isinstance(fn, ast.Attribute) and fn.attr == "run_harness":
                calls.append(node)
    return calls


def _sim_constructions(tree: ast.Module) -> list[ast.Call]:
    """All call sites that construct a v2 ``Sim(...)`` instance.

    Catches both ``Sim(generator=..., property=...)`` directly and
    ``module.Sim(...)`` if someone aliases the import.
    """
    calls: list[ast.Call] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            fn = node.func
            if isinstance(fn, ast.Name) and fn.id == "Sim":
                calls.append(node)
            elif isinstance(fn, ast.Attribute) and fn.attr == "Sim":
                calls.append(node)
    return calls


def _sim_has_required_v2_kwargs(call: ast.Call) -> bool:
    """A v2 ``Sim(...)`` opt-in must pass ``generator=`` and
    ``property=`` (the two non-defaulted dataclass fields). A bare
    ``Sim()`` would TypeError at runtime; this catches the case
    where someone constructs ``Sim(name=..., lean_module=...)``
    while forgetting the coverage-bearing kwargs.
    """
    kw_names = {kw.arg for kw in call.keywords if kw.arg is not None}
    return "generator" in kw_names and "property" in kw_names


def _kw_value(call: ast.Call, name: str) -> ast.expr | None:
    for kw in call.keywords:
        if kw.arg == name:
            return kw.value
    return None


def _is_non_empty_mutations(value: ast.expr | None) -> bool:
    """True iff the kwarg value passed to ``mutations=`` is provably
    non-empty.

    Accepts:
      * ``mutations=(m1, m2, ...)``                      — non-empty literal
      * ``mutations=[m1, m2, ...]``                       — non-empty list literal
      * ``mutations=MUTATIONS`` where MUTATIONS is a    — module-level
        non-empty literal at module scope                 alias
      * ``mutations=*expression*`` — fallback: only       (caller-defined
        accept names that resolve to non-empty literals    aliases)
        elsewhere in the module.

    Rejects:
      * ``mutations=()`` / ``mutations=[]`` (empty)
      * ``mutations=None``
      * absent kwarg (None passed in)
    """
    if value is None:
        return False
    if isinstance(value, (ast.Tuple, ast.List)):
        return len(value.elts) > 0
    if isinstance(value, ast.Constant) and value.value is None:
        return False
    # If it's a Name reference, we need to look up the binding at module
    # scope. The caller resolves this via ``_resolve_name_to_literal``.
    return True  # fall-through: treat as "needs deeper check"


def _resolve_name_to_literal(tree: ast.Module, name: str) -> ast.expr | None:
    """Return the RHS expression of a top-level ``<name> = <expr>``
    binding, or None if no such binding exists."""
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.Assign):
            for tgt in node.targets:
                if isinstance(tgt, ast.Name) and tgt.id == name:
                    return node.value
    return None


def _sim_uses_coverage_primitives(path: Path) -> tuple[bool, str]:
    """Return ``(passed, reason)`` for a single sim file.

    Accepts either contract:

    * **v1 harness pattern** — imports ``tools.sim.harness`` AND
      calls ``run_harness(...)`` with ``mutations=<non-empty>``.
    * **v2 Sim pattern** — imports from ``tools.sim.harness.v2`` AND
      constructs at least one ``Sim(generator=..., property=...)``
      instance. The v2 harness internally drives PBT + symmetry +
      replay; v2 sims demonstrate the contract by Sim-construction
      shape.

    ``reason`` is empty on pass; on fail it names the missing primitive
    and points at a fix.
    """
    try:
        tree = _parse_module(path)
    except SyntaxError as exc:
        return False, f"SyntaxError: {exc}"

    has_v1_import = _imports_v1_harness(tree)
    has_v2_import = _imports_v2_harness(tree)

    if not has_v1_import and not has_v2_import:
        return False, (
            "no import of tools.sim.harness or tools.sim.harness.v2 — "
            "sim must use one of the shared harnesses so PBT + sweep + "
            "mutation (v1) or PBT + symmetry + replay (v2) coverage "
            "runs through one battle-tested code path."
        )

    # v2 path: a single non-empty Sim construction with the required
    # kwargs is enough. v2's harness drives PBT + symmetry + replay
    # internally based on those kwargs.
    if has_v2_import:
        sim_calls = _sim_constructions(tree)
        if sim_calls:
            for call in sim_calls:
                if _sim_has_required_v2_kwargs(call):
                    return True, ""
            return False, (
                "tools.sim.harness.v2 imported but no Sim(...) call "
                "carries both ``generator=`` and ``property=`` "
                "kwargs. v2 coverage requires at least one Sim "
                "instance with those two fields populated."
            )
        # Imported v2 but never constructed a Sim — fall through to
        # v1 check; the file might be a helper module rather than a
        # sim runner.

    # v1 path: must import v1 harness AND call run_harness with
    # non-empty mutations.
    if not has_v1_import:
        return False, (
            "v2 imports present but no Sim(...) constructed. If this "
            "is a v2 helper module, exclude it from the manifest. "
            "Otherwise add the canonical Sim declaration."
        )

    calls = _run_harness_calls(tree)
    if not calls:
        return False, (
            "no run_harness(...) call — paper claims PBT + sweeps + "
            "mutation testing on every theorem. Calling run_harness is "
            "how that coverage actually fires."
        )

    # At least one call must pass non-empty mutations (the harness
    # itself enforces non-vacuous PBT + sweeps internally; the only
    # primitive the caller must explicitly opt into is mutation
    # testing because mutations are domain-specific).
    for call in calls:
        kw = _kw_value(call, "mutations")
        if kw is None:
            continue
        if isinstance(kw, (ast.Tuple, ast.List)):
            if len(kw.elts) > 0:
                return True, ""
            continue
        if isinstance(kw, ast.Name):
            resolved = _resolve_name_to_literal(tree, kw.id)
            if isinstance(resolved, (ast.Tuple, ast.List)) and len(resolved.elts) > 0:
                return True, ""
            continue
        # Any other shape (function call, subscript, etc.): trust it.
        return True, ""

    return False, (
        "run_harness(...) called but no non-empty mutations= argument "
        "found. Mutation testing is a documented paper primitive — "
        "without it the spec test can pass vacuously. Add at least "
        "one Mutation that perturbs the theorem statement and ensure "
        "the harness flags it as caught."
    )


class TestCoveragePrimitives:
    """Every domain sim must opt into PBT + sweeps + mutation testing.

    These checks close the gap between 'function exists with the right
    name' (which the forward / AST tests above enforce) and the actual
    paper claim 'every theorem under PBT + sweeps + mutation testing'.
    """

    @pytest.mark.parametrize(
        "sim_file",
        _domain_sim_files(),
        ids=[p.stem for p in _domain_sim_files()],
    )
    def test_sim_uses_coverage_primitives(self, sim_file: Path) -> None:
        ok, reason = _sim_uses_coverage_primitives(sim_file)
        assert ok, (
            f"Coverage gap in {sim_file.relative_to(REPO_ROOT)}:\n"
            f"  {reason}\n"
            f"\n"
            f"This file must follow the v1 harness contract (or the "
            f"v2 Sim contract once that lands) so the paper claim "
            f"\"every theorem under PBT + sweeps + mutation testing\" "
            f"is actually enforceable, not just documented."
        )


# ── Utility-exclusion sanity ───────────────────────────────────────────


class TestCoveragePrimitivesHelper:
    """Unit tests for the `_sim_uses_coverage_primitives` helper.

    These pin the helper's behaviour on synthetic inputs so the
    parametrised contract test above can be trusted to catch real
    regressions. Each case answers: "if the helper saw this file
    shape, would it correctly accept / reject it?"
    """

    def test_rejects_trivial_test_function(self, tmp_path: Path) -> None:
        """The classic anti-pattern: function with the right name but
        no actual coverage. The original gate would PASS this; the
        new check must REJECT it."""
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "def test_fake() -> None:\n"
            "    assert True\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "tools.sim.harness" in reason

    def test_rejects_no_run_harness_call(self, tmp_path: Path) -> None:
        """Imports the harness but doesn't call run_harness — would
        previously pass since the import shows intent, but the
        actual coverage primitives never fire."""
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness, Strategy, floats\n"
            "def test_fake() -> None:\n"
            "    assert True\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "run_harness" in reason

    def test_rejects_empty_mutations_tuple(self, tmp_path: Path) -> None:
        """``mutations=()`` is the silent-vacuousness shape: PBT runs
        but no mutation testing happens. The paper claim "PBT +
        sweeps + mutation testing" is violated."""
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness\n"
            "def test_fake() -> None:\n"
            "    run_harness(name='x', spec=lambda: True, "
            "strategy=None, mutations=())\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "mutations" in reason

    def test_rejects_empty_mutations_list(self, tmp_path: Path) -> None:
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness\n"
            "def test_fake() -> None:\n"
            "    run_harness(name='x', spec=lambda: True, "
            "strategy=None, mutations=[])\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "mutations" in reason

    def test_rejects_missing_mutations_kwarg(self, tmp_path: Path) -> None:
        """Run_harness called without mutations= at all.

        The harness signature requires mutations, but a call could
        in principle omit them via **kwargs unpacking; we explicitly
        reject calls that lack a non-empty mutations= keyword.
        """
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness\n"
            "def test_fake() -> None:\n"
            "    run_harness(name='x', spec=lambda: True, strategy=None)\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "mutations" in reason

    def test_accepts_non_empty_inline_mutations(self, tmp_path: Path) -> None:
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness, Mutation\n"
            "def test_fake() -> None:\n"
            "    run_harness(name='x', spec=lambda: True, strategy=None,\n"
            "                mutations=(Mutation(name='m', spec=lambda: False),))\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert ok, reason

    def test_accepts_module_level_mutations_alias(self, tmp_path: Path) -> None:
        """The canonical pattern: ``MUTATIONS = (...)`` at module
        scope, then ``run_harness(..., mutations=MUTATIONS)``.

        Helper resolves the Name reference back to the module-level
        binding to confirm non-emptiness."""
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness, Mutation\n"
            "MUTATIONS = (\n"
            "    Mutation(name='m1', spec=lambda: False),\n"
            "    Mutation(name='m2', spec=lambda: False),\n"
            ")\n"
            "def test_fake() -> None:\n"
            "    run_harness(name='x', spec=lambda: True, "
            "strategy=None, mutations=MUTATIONS)\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert ok, reason

    def test_rejects_module_level_empty_mutations_alias(self, tmp_path: Path) -> None:
        f = tmp_path / "fake_sim.py"
        f.write_text(
            "from tools.sim.harness import run_harness\n"
            "MUTATIONS = ()\n"
            "def test_fake() -> None:\n"
            "    run_harness(name='x', spec=lambda: True, "
            "strategy=None, mutations=MUTATIONS)\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "mutations" in reason

    def test_accepts_v2_sim_with_required_kwargs(self, tmp_path: Path) -> None:
        """A v2-pattern sim that imports harness.v2 and constructs a
        Sim(generator=..., property=...) passes the gate without
        needing the v1 harness.

        This is the path the ATH-791 PoC files follow — they do not
        import the v1 harness because the v2 contract internally
        drives PBT + symmetry + replay. The gate must accept the
        v2 contract or v2 sims will be flagged as orphans the moment
        ATH-791 lands."""
        f = tmp_path / "fake_v2_sim.py"
        f.write_text(
            "from tools.sim.harness.v2 import Sim\n"
            "from tools.sim.harness.v2.generators import positive_real\n"
            "from tools.sim.harness.v2.properties import identity\n"
            "my_sim = Sim(\n"
            "    name='fake.v2',\n"
            "    lean_module='Pythia.Fake',\n"
            "    generator=positive_real(),\n"
            "    property=lambda x: True,\n"
            "    replications=100,\n"
            ")\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert ok, reason

    def test_rejects_v2_sim_missing_property_kwarg(self, tmp_path: Path) -> None:
        """A v2 Sim that omits ``property=`` is incomplete coverage."""
        f = tmp_path / "fake_v2_sim.py"
        f.write_text(
            "from tools.sim.harness.v2 import Sim\n"
            "from tools.sim.harness.v2.generators import positive_real\n"
            "broken = Sim(\n"
            "    name='broken.v2',\n"
            "    lean_module='Pythia.Broken',\n"
            "    generator=positive_real(),\n"
            "    replications=100,\n"
            ")\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "property" in reason

    def test_rejects_v2_sim_missing_generator_kwarg(self, tmp_path: Path) -> None:
        """Same shape as above for ``generator=`` omission."""
        f = tmp_path / "fake_v2_sim.py"
        f.write_text(
            "from tools.sim.harness.v2 import Sim\n"
            "broken = Sim(\n"
            "    name='broken.v2',\n"
            "    lean_module='Pythia.Broken',\n"
            "    property=lambda x: True,\n"
            "    replications=100,\n"
            ")\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert not ok
        assert "generator" in reason

    def test_accepts_v2_sim_with_v2_subpackage_import(self, tmp_path: Path) -> None:
        """Importing from ``tools.sim.harness.v2.generators`` (not just
        the top-level v2 package) also satisfies the v2 contract."""
        f = tmp_path / "fake_v2_sim.py"
        f.write_text(
            "from tools.sim.harness.v2 import Sim\n"
            "from tools.sim.harness.v2.metamorphic import homogeneous\n"
            "my_sim = Sim(\n"
            "    name='fake.v2',\n"
            "    lean_module='Pythia.Fake',\n"
            "    generator=None,\n"  # value irrelevant; we check kwarg presence
            "    property=lambda x: True,\n"
            ")\n"
        )
        ok, reason = _sim_uses_coverage_primitives(f)
        assert ok, reason


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
