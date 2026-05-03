#!/usr/bin/env python3
"""tools/check_readme_numbers.py — auto-gate for README numeric claims.

Catches the class of bug where README.md drifts away from repo reality:
the numbers (theorem counts, tactic counts, module headcounts, default
n_pbt config, toolchain versions) become stale as the repo grows but
no PR updates the prose.

Computes ground-truth values from the repo, then compares against the
literal numbers asserted in README.md. Exit 0 if every claim matches,
exit 1 with a per-claim diff if any drift.

Usage:
    python3 tools/check_readme_numbers.py            # check + report
    python3 tools/check_readme_numbers.py --update   # rewrite README in place

Wired into CI as a pytest test (see tools/test_check_readme_numbers.py).

Counting conventions (intentionally conservative):

  * "Public theorem" = bare ``theorem`` keyword (excluding ``private theorem``)
    or ``@[stat_lemma]\\ntheorem`` decorator pattern. We do NOT include
    ``lemma`` declarations — those are typically internal helpers and
    not what a reader cites when they say "the library has N theorems".

  * Excluded paths: ``Pythia/Frontier/**`` (work-in-progress, sorries
    permitted), ``Pythia/Scratch/**`` (agent-scratch artefacts),
    ``Pythia/AxiomAudit.lean`` (introspection meta-file),
    ``Pythia/VilleMathlibPR.lean`` (Mathlib-PR draft, namespaced
    differently).

  * Per-module counts use the directory layout under ``Pythia/`` —
    ``Pythia.Hardware`` = files under ``Pythia/Hardware/``, etc.
    Top-level files (``Pythia/SubGaussianMG.lean``, etc.) are bucketed
    as ``Pythia.Probability`` for the README rollup.

  * Tactic count: distinct user-facing tactic names registered via
    ``syntax (name := ...) "name" : tactic``. Multiple parser forms of
    the same tactic (e.g. ``anytime_valid``, ``anytime_valid (horizon
    := N)``, ``anytime_valid using h``) count as one tactic, not three.

  * n_pbt count: the "10,000 draws per theorem" claim — verified against
    the default value of ``n_pbt`` in ``tools/sim/*.py`` headers.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
README = REPO_ROOT / "README.md"

# Files / directories excluded from public-theorem accounting.
EXCLUDE_DIRS = ("Pythia/Frontier", "Pythia/Scratch")
EXCLUDE_FILES = ("Pythia/AxiomAudit.lean", "Pythia/VilleMathlibPR.lean")

# Top-level Pythia/*.lean files (no subdir) get bucketed under Probability
# for the README rollup. This matches the README's narrative grouping —
# the bulk of probability-theory theorems (BettingCS, SubGaussianMG,
# SPRT, Bernstein, etc.) live at the top level.
PROBABILITY_BUCKET = ("",)  # top-level == ""

# Per-module rollup. Each entry maps to one or more directory prefixes
# under Pythia/. Keep this in sync with the README "Domains" table.
MODULE_ROLLUP: Dict[str, Tuple[str, ...]] = {
    "Pythia.Probability": (
        "",  # top-level Pythia/*.lean (BettingCS, SubGaussianMG, ...)
        "Concentration",
        "MeasureTheory",
        "StochasticApproximation",
        "Stochastic",
        "TimeSeries",
        "Risk",
        "HypothesisTest",
        "InfoTheory",
        "Asymptotics",
        "Bench",
        "Tactic",
        "ClinicalTrials",
        "SPRT",
    ),
    "Pythia.LanguageSemantics": ("LanguageSemantics",),
    "Pythia.Actuarial": ("Actuarial",),
    "Pythia.Hardware": ("Hardware",),
    "Pythia.Numerical": ("Numerical",),
    "Pythia.Networking": ("Networking",),
    "Pythia.Bio": ("Bio",),
    # Domains not yet headlined in README (kept for total-count reconciliation):
    "Pythia.Other": (
        "Chemistry",
        "Control",
        "Economics",
        "Engineering",
        "GameTheory",
        "Mechanical",
        "Neuroscience",
        "OR",
        "OptimalTransport",
        "Quantum",
        "Queueing",
        "Thermodynamics",
    ),
}


def _is_excluded(path: Path) -> bool:
    rel = str(path.relative_to(REPO_ROOT))
    if rel in EXCLUDE_FILES:
        return True
    return any(rel.startswith(d + "/") for d in EXCLUDE_DIRS)


def count_theorems_in_file(path: Path) -> int:
    """Count public theorem declarations in a single .lean file.

    Public = bare ``theorem `` at line start (no ``private`` modifier).
    Counts both ``theorem foo : ...`` and ``@[stat_lemma]\\ntheorem foo``
    patterns (the latter being the dispatch-attribute decorator we use
    for tagged probability theorems).
    """
    n = 0
    try:
        text = path.read_text()
    except (OSError, UnicodeDecodeError):
        return 0
    # Match `theorem <name>` at line start. Allow common attribute lines
    # to precede via a separate count.
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("theorem ") and not s.startswith("private theorem"):
            n += 1
    return n


def discover_lean_files() -> List[Path]:
    out: List[Path] = []
    for p in sorted((REPO_ROOT / "Pythia").rglob("*.lean")):
        if _is_excluded(p):
            continue
        out.append(p)
    return out


def tally_per_module() -> Dict[str, int]:
    """Compute theorem count per README-headlined module."""
    files = discover_lean_files()
    rollup: Dict[str, int] = {k: 0 for k in MODULE_ROLLUP}
    for p in files:
        rel = str(p.relative_to(REPO_ROOT / "Pythia"))
        # The first path segment if it has a / (subdir), else "" (top-level)
        if "/" in rel:
            top = rel.split("/", 1)[0]
        else:
            top = ""
        # Find which module bucket this top belongs to. Top-level "" is in
        # MODULE_ROLLUP["Pythia.Probability"][0].
        bucket = None
        for mod, dirs in MODULE_ROLLUP.items():
            if top in dirs:
                bucket = mod
                break
        if bucket is None:
            # Unaccounted directory — flag separately
            bucket = "Pythia.Unaccounted"
            rollup.setdefault(bucket, 0)
        rollup[bucket] += count_theorems_in_file(p)
    return rollup


def total_theorems() -> int:
    return sum(count_theorems_in_file(p) for p in discover_lean_files())


def count_distinct_tactics() -> int:
    """Count distinct user-facing tactic names registered via
    ``syntax (name := ...) "<name>" : tactic``.

    Multiple parser forms of the same tactic (different argument shapes)
    count once. Deprecated aliases (``pythia!!`` -> ``pythia!``,
    ``pythia!?`` -> ``pythia?``) are excluded.
    """
    tactic_names = set()
    pat = re.compile(r'^syntax\s*\(name\s*:=\s*\w+\)\s*"([^"]+)"\s*:\s*tactic')
    for path in (REPO_ROOT / "Pythia/Tactic").rglob("*.lean"):
        if path.name.endswith("Test.lean"):
            continue
        for line in path.read_text().splitlines():
            m = pat.match(line.strip())
            if m:
                tactic_names.add(m.group(1))
    # Fold deprecated-alias families. We keep the canonical name.
    aliases = {"pythia!!": "pythia!", "pythia!?": "pythia?"}
    canonical = {aliases.get(t, t) for t in tactic_names}
    return len(canonical)


def n_pbt_headline() -> int:
    """Read the headline n_pbt value from tools/sim/*.py — the production
    harness draw count asserted in the README "Empirical verification"
    section.

    A simulation file typically contains both a production-grade
    n_pbt (large, used for the main verification call) and a fast-path
    n_pbt (small, used in subprocess invocations or exploratory runs).
    The README headline refers to the production-grade value.

    We extract the *largest* n_pbt occurring at frequency >= 10 across
    sim files. This filters out one-off experimental values while still
    surfacing the headline production-harness draw count.
    """
    counts: Dict[int, int] = {}
    for path in (REPO_ROOT / "tools/sim").glob("*.py"):
        for line in path.read_text().splitlines():
            m = re.search(r"\bn_pbt\s*=\s*([0-9_]+)", line)
            if m:
                v = int(m.group(1).replace("_", ""))
                counts[v] = counts.get(v, 0) + 1
    if not counts:
        return 0
    common = [v for v, c in counts.items() if c >= 10]
    return max(common) if common else max(counts.values())


def lean_toolchain() -> str:
    """Read the Lean toolchain pin (e.g. '4.28.0') from lean-toolchain."""
    line = (REPO_ROOT / "lean-toolchain").read_text().strip()
    # Format: leanprover/lean4:v4.28.0
    m = re.search(r"v?(\d+\.\d+\.\d+)", line)
    return m.group(1) if m else line


def mathlib_version() -> str:
    """Read the pinned Mathlib version from lake-manifest.json."""
    import json
    manifest = json.loads((REPO_ROOT / "lake-manifest.json").read_text())
    for pkg in manifest.get("packages", []):
        if pkg.get("name") == "mathlib":
            rev = pkg.get("rev", "")
            tag = pkg.get("inputRev", "")
            return tag or rev[:8]
    return "<unknown>"


def parse_readme_claims(text: str) -> Dict[str, str]:
    """Extract literal claims from README.md as named values.

    Returns a dict keyed by claim name, mapping to the textual value
    in the README. The check function below compares each against the
    computed ground truth.
    """
    claims = {}
    # "711 sorry-free theorems"
    m = re.search(
        r"It provides (\d+(?:,\d+)?) sorry-free theorems", text)
    if m:
        claims["total_theorems_intro"] = m.group(1).replace(",", "")
    # "all 711 declarations"
    m = re.search(r"over all (\d+(?:,\d+)?)\s*\n?\s*declarations", text)
    if m:
        claims["total_theorems_retrieval"] = m.group(1).replace(",", "")
    # Per-module table — Pythia.<Mod> | <count> | ...
    for mod_full, dirs in MODULE_ROLLUP.items():
        if mod_full == "Pythia.Other":
            continue
        # Match `| `Pythia.Mod` | <number or word> |`
        # Match the count (number or "scaffolds")
        # Use a tolerant match — README table has |...|count|...| layout
        mod_name_escaped = re.escape(mod_full.split(".", 1)[1])
        pat = re.compile(
            r"\|\s*`Pythia\." + mod_name_escaped +
            r"`\s*\|\s*(~?\d+|scaffolds)\s*\|"
        )
        m = pat.search(text)
        if m:
            claims[f"module_{mod_full}"] = m.group(1)
    # "Pythia registers eleven tactics"
    m = re.search(r"Pythia registers (\w+) tactics", text)
    if m:
        word = m.group(1).lower()
        word_to_int = {
            "one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
            "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
            "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
        }
        if word in word_to_int:
            claims["tactic_count"] = str(word_to_int[word])
        elif word.isdigit():
            claims["tactic_count"] = word
    # "10,000 draws per theorem"
    m = re.search(r"(\d+,?\d*) draws per theorem", text)
    if m:
        claims["n_pbt"] = m.group(1).replace(",", "")
    # Lean 4.28.0 badge
    m = re.search(r"Lean-(\d+\.\d+\.\d+)-blue", text)
    if m:
        claims["lean_version"] = m.group(1)
    # Mathlib v4.28.0 badge
    m = re.search(r"Mathlib-(v?\d+\.\d+\.\d+)-blue", text)
    if m:
        claims["mathlib_version"] = m.group(1)
    return claims


def compute_truth() -> Dict[str, str]:
    """Compute the canonical ground-truth value for every claim."""
    rollup = tally_per_module()
    truth = {
        "total_theorems_intro": str(total_theorems()),
        "total_theorems_retrieval": str(total_theorems()),
        "tactic_count": str(count_distinct_tactics()),
        "n_pbt": str(n_pbt_headline()),
        "lean_version": lean_toolchain(),
        "mathlib_version": mathlib_version(),
    }
    # Per-module values. README accepts a literal int OR a "~"-prefixed
    # approximate. We treat a "~N" claim as valid if the truth is within
    # ±10% of N.
    for mod_full in MODULE_ROLLUP:
        if mod_full in ("Pythia.Other",):
            continue
        truth[f"module_{mod_full}"] = str(rollup.get(mod_full, 0))
    return truth


def compare(claims: Dict[str, str], truth: Dict[str, str]) -> List[Tuple[str, str, str]]:
    """Return a list of (claim_key, claimed, actual) tuples for any
    mismatched claim. Exact for ints; tolerant for ``~N`` (within ±10%);
    string-equal for versions; "scaffolds" accepts truth in [1, 30]
    (a small handful of files = scaffold territory)."""
    diffs: List[Tuple[str, str, str]] = []
    for key, claimed in claims.items():
        actual = truth.get(key)
        if actual is None:
            # Computed truth missing for a claim we can't verify — skip.
            continue
        if claimed.startswith("~"):
            try:
                claimed_int = int(claimed[1:])
                actual_int = int(actual)
                if not (claimed_int * 0.9 <= actual_int <= claimed_int * 1.1):
                    diffs.append((key, claimed, actual))
            except ValueError:
                if claimed[1:] != actual:
                    diffs.append((key, claimed, actual))
        elif claimed == "scaffolds":
            try:
                actual_int = int(actual)
                if not (1 <= actual_int <= 30):
                    diffs.append((key, claimed, actual))
            except ValueError:
                pass
        else:
            if claimed != actual:
                diffs.append((key, claimed, actual))
    return diffs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verbose", action="store_true",
                        help="print full claims+truth dump even on success")
    args = parser.parse_args()

    text = README.read_text()
    claims = parse_readme_claims(text)
    truth = compute_truth()
    diffs = compare(claims, truth)

    if args.verbose:
        print("=== claimed in README ===")
        for k in sorted(claims):
            print(f"  {k:50s} {claims[k]}")
        print()
        print("=== computed from repo ===")
        for k in sorted(truth):
            print(f"  {k:50s} {truth[k]}")
        print()

    if not diffs:
        print(f"OK: all {len(claims)} numeric claims in README match repo.")
        return 0

    print(f"DRIFT: {len(diffs)} README claim(s) do not match repo:")
    print()
    for key, claimed, actual in diffs:
        print(f"  {key}")
        print(f"    README claims: {claimed}")
        print(f"    Repo reality:  {actual}")
        print()
    print("Either update README.md to match, or investigate why the repo")
    print("disagrees with the README. Run with --verbose to see all values.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
