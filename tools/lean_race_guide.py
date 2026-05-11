#!/usr/bin/env python3
"""Quick dogfood guide: kairos lean_race replaces Aristotle.

Usage (from kairos-stats-lean repo root):

    python3 tools/lean_race_guide.py Pythia/Frontier/MatrixBernstein.lean

Or as a library:

    from tools.lean_race_guide import race_sorry

    result = race_sorry(
        sorry_file="Pythia/Frontier/MatrixBernstein.lean",
        theorem_name="matrixBernstein_self_adjoint",
    )
    if result.proved:
        print(result.closing_candidate)

Config reference (CycleTarget fields):
    imports:    list of module names, e.g. ["Mathlib"]  (NOT "import Mathlib")
    opens:      list of namespaces, e.g. ["Finset", "BigOperators"]
    header:     theorem statement WITHOUT := or := by
    lake_project: absolute path to repo root
    module_path:  dotted path for scratch file, e.g. "Pythia.Scratch.Race01"
    scratch_namespace: same as module_path

Key lessons from dogfood (2026-05-11):
    1. imports is a LIST, not a string.  ["Mathlib"] not "import Mathlib"
    2. module_path must NOT be "Pythia" (overwrites root module).
       Use "Pythia.Scratch.<Name>" for scratch proofs.
    3. Gemini Flash works (GEMINI_API_KEY). Zero Azure/Foundry cost.
    4. Drafters self-correct: round 1 may fail, round 2 fixes arity/naming.
    5. max_rounds=4 gives the drafter enough attempts for medium proofs.
"""
from __future__ import annotations

import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def race_sorry(
    sorry_file: str,
    theorem_name: str | None = None,
    max_rounds: int = 4,
    drafter_model: str = "gemini/gemini-2.5-flash",
) -> "RaceResult":
    os.environ.setdefault("KAIROS_DEV_NO_LICENSE", "1")

    from kairos.lean_cycle import CycleTarget
    from kairos.lean_orchestrate import ModelClientDrafter, race

    text = (REPO_ROOT / sorry_file).read_text()

    if theorem_name is None:
        decls = re.findall(r"(?:theorem|lemma)\s+(\w+)", text)
        sorry_decls = []
        for d in decls:
            idx = text.index(d)
            after = text[idx:]
            if "sorry" in after.split("\n\ntheorem")[0].split("\n\nlemma")[0]:
                sorry_decls.append(d)
        theorem_name = sorry_decls[0] if sorry_decls else decls[0]

    ns_match = re.search(r"namespace\s+([\w.]+)", text)
    ns = ns_match.group(1) if ns_match else "Pythia.Scratch"

    imports = re.findall(r"^import\s+(\S+)", text, re.MULTILINE)
    opens = re.findall(r"^open\s+(.+)$", text, re.MULTILINE)

    thm_match = re.search(
        rf"((?:theorem|lemma)\s+{re.escape(theorem_name)}\b.*?)(?::=\s*by\s+sorry|:=\s+sorry)",
        text,
        re.DOTALL,
    )
    header = thm_match.group(1).strip() if thm_match else f"theorem {theorem_name}"

    scratch_ns = f"Pythia.Scratch.Race_{theorem_name}"

    target = CycleTarget(
        tid=theorem_name,
        imports=imports or ["Mathlib"],
        opens=opens or [],
        header=header,
        lake_project=str(REPO_ROOT),
        module_path=scratch_ns,
        scratch_namespace=scratch_ns,
        timeout_per_attempt=120,
    )

    drafter = ModelClientDrafter(alias="drafter", model_id=drafter_model)

    print(f"Racing {theorem_name} with {drafter_model} (max_rounds={max_rounds})...")
    result = race(
        target=target,
        drafters=[drafter],
        max_rounds=max_rounds,
        preflight=False,
    )

    if result.proved:
        print(f"PROVED by {result.first_closer_alias}")
        print(f"Proof: {result.closing_candidate}")
    else:
        print("NOT PROVED")
        for alias, outcome in result.outcomes_by_drafter.items():
            for r in outcome.rounds:
                status = "OK" if r.proof_result.compiles else "FAIL"
                print(f"  Round {r.round} [{status}]: {r.candidate[:80] if r.candidate else 'None'}")

    return result


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(0)
    sorry_file = sys.argv[1]
    theorem_name = sys.argv[2] if len(sys.argv) > 2 else None
    race_sorry(sorry_file, theorem_name)
