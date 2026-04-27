"""tools/sim/check_axiom_audit.py — CI script that validates lake's
axiom audit output against the expected-coverage manifest.

Usage::

    lake env lean Pythia/AxiomAudit.lean > axiom-audit.txt 2>&1
    python3 -m tools.sim.check_axiom_audit axiom-audit.txt

Returns exit code 0 if every theorem in
:data:`tools.sim.axiom_audit_manifest.EXPECTED_AUDITED_THEOREMS`
appears as a substring of the lake output, else exit code 1 with
a missing-theorems list.

Why this is stronger than ``grep -c "axioms"`` in the CI YAML:

* Acts on lake's actual output (authoritative), not on the Lean
  source (which can drift from what lake emits if imports break
  or definitions move).
* Names each missing theorem explicitly so a CI failure tells the
  reader exactly which directive was lost.
* The manifest is a reviewable Python module, not a regex pattern.

Why this is a separate Python script and not a pytest:
   pytest would either need to invoke lake itself (slow, requires
   lake on the test machine) or ingest a pre-built artifact
   (couples test discovery to CI). Keeping it as a standalone
   script lets CI invoke lake once and let pytest validate the
   manifest schema independently.
"""
from __future__ import annotations

import sys
from pathlib import Path

from tools.sim.axiom_audit_manifest import EXPECTED_AUDITED_THEOREMS


def find_missing(audit_output: str, expected: frozenset[str]) -> list[str]:
    """Return theorems from ``expected`` that do not appear as a
    substring in ``audit_output``. Uses a substring check because
    Lean's emitted output format (``axioms used in '<name>':`` /
    ``'<name>' depends on axioms:``) is version-dependent; a
    substring on the declaration name is stable across versions.
    """
    missing: list[str] = []
    for name in sorted(expected):
        if name not in audit_output:
            missing.append(name)
    return missing


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(
            "usage: python3 -m tools.sim.check_axiom_audit <audit-output-file>",
            file=sys.stderr,
        )
        return 2

    audit_path = Path(argv[1])
    if not audit_path.is_file():
        print(f"error: audit output file not found: {audit_path}", file=sys.stderr)
        return 2

    audit_output = audit_path.read_text(encoding="utf-8")
    missing = find_missing(audit_output, EXPECTED_AUDITED_THEOREMS)

    if missing:
        print(
            f"FAIL: {len(missing)} expected theorem(s) missing from axiom audit output:",
            file=sys.stderr,
        )
        for name in missing:
            print(f"  - {name}", file=sys.stderr)
        print(
            "\nEither (a) lake failed to emit `#print axioms` for these "
            "decls (check audit-output for an earlier error), or (b) "
            "someone removed `#print axioms` directives from "
            "Pythia/AxiomAudit.lean without bumping "
            "EXPECTED_AUDITED_THEOREMS in this PR.\n"
            "Each missing entry breaks the AI4MATH 2026 paper claim "
            "\"every public theorem axiom-clean against the standard "
            "kernel set\".",
            file=sys.stderr,
        )
        return 1

    print(
        f"OK: all {len(EXPECTED_AUDITED_THEOREMS)} expected theorems "
        f"appear in axiom audit output."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
