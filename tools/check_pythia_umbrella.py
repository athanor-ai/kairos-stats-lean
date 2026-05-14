#!/usr/bin/env python3
"""Verify every Pythia/**/*.lean file is in the transitive import closure of Pythia.lean.

The Lean Build + Axiom Audit workflow runs a per-file sweep
(`lake env lean Pythia/**/*.lean`) AFTER `lake build`. If a leaf module
is not pulled into the umbrella via `Pythia.lean`, `lake build` will
still pass (the orphan leaf builds standalone with no demand), but the
per-file sweep fails on the first file that imports the orphan because
the orphan's olean was never built.

This script catches that class statically (1 second) so the pre-push
hook can refuse a push that introduces an orphan, instead of letting
CI catch it after a 15-minute Lean build.

Exit code 0 if every file is reachable from `Pythia.lean`; exit code 1
with a list of orphans otherwise.

Exclusions match the per-file sweep in .github/workflows/lean-build.yml:
- VilleMathlibPR.lean (Mathlib-PR-style draft, namespaced under MeasureTheory)
- Pythia/Scratch/** (agent scratch)
- **/Tactic/*Test.lean (test files use example blocks)
- Pythia/AxiomAudit.lean (runtime-only #print-axioms harness)
- Pythia.lean itself (the umbrella file)
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PYTHIA_ROOT = REPO_ROOT / "Pythia"
UMBRELLA = REPO_ROOT / "Pythia.lean"

IMPORT_RE = re.compile(r"^\s*import\s+(Pythia(?:\.[A-Za-z0-9_]+)+)\s*$")

EXCLUDE_FILE_NAMES = {"VilleMathlibPR.lean", "AxiomAudit.lean"}


def is_excluded(path: Path) -> bool:
    if path.name in EXCLUDE_FILE_NAMES:
        return True
    parts = path.relative_to(REPO_ROOT).parts
    if "Scratch" in parts:
        return True
    if "Tactic" in parts and path.name.endswith("Test.lean"):
        return True
    return False


def path_to_module(path: Path) -> str:
    rel = path.relative_to(REPO_ROOT)
    return ".".join(rel.with_suffix("").parts)


def module_to_path(module: str) -> Path:
    parts = module.split(".")
    return REPO_ROOT / Path(*parts[:-1]) / f"{parts[-1]}.lean"


def parse_imports(lean_file: Path) -> list[str]:
    if not lean_file.is_file():
        return []
    imports: list[str] = []
    try:
        for line in lean_file.read_text(encoding="utf-8").splitlines():
            m = IMPORT_RE.match(line)
            if m:
                imports.append(m.group(1))
    except (OSError, UnicodeDecodeError):
        pass
    return imports


def closure_from(root_module: str) -> set[str]:
    """BFS over the import graph starting at root_module."""
    seen: set[str] = set()
    stack = [root_module]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = module_to_path(mod)
        for imp in parse_imports(path):
            if imp not in seen:
                stack.append(imp)
    return seen


def main() -> int:
    if not UMBRELLA.is_file():
        print(f"ERROR: umbrella file not found at {UMBRELLA}", file=sys.stderr)
        return 1

    reachable = closure_from("Pythia")

    orphans: list[Path] = []
    for lean_file in sorted(PYTHIA_ROOT.rglob("*.lean")):
        if is_excluded(lean_file):
            continue
        module = path_to_module(lean_file)
        if module not in reachable:
            orphans.append(lean_file)

    if orphans:
        print(
            f"ERROR: {len(orphans)} Pythia file(s) not reachable from Pythia.lean umbrella.",
            file=sys.stderr,
        )
        print(
            "These will silently miss `lake build` and fail the CI per-file sweep.",
            file=sys.stderr,
        )
        print("Add an `import <module>` line to Pythia.lean for each:", file=sys.stderr)
        for path in orphans:
            module = path_to_module(path)
            print(f"  import {module}    # {path.relative_to(REPO_ROOT)}", file=sys.stderr)
        return 1

    file_count = sum(1 for _ in PYTHIA_ROOT.rglob("*.lean") if not is_excluded(_))
    print(f"OK: all {file_count} Pythia/*.lean files reachable from Pythia.lean umbrella.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
