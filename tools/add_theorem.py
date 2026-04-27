#!/usr/bin/env python3
"""tools/add_theorem.py — scaffold a new pythia theorem.

Generates the L0 (Lean) + L1 (Python harness) file pair from
templates and appends a manifest entry. The proof tactic is left as
`sorry` so a sonnet sub-agent (or a human) can fill it in via lake
build iteration.

Usage:

    tools/add_theorem.py \\
        --domain Economics \\
        --name solow_steady_state_pos \\
        --statement 'theorem solow_steady_state_pos {...} : ...' \\
        --summary 'Solow growth steady state k* > 0' \\
        --mathlib-status novel

Optional flags:

    --imports 'Mathlib,Pythia.Tactic.Pythia'  (default)
    --opens   'Real'                          (default)
    --reference 'Solow, R.M. QJE 70(1) (1956)' (repeatable)
    --strategy 'k=floats(0.01,1e3,log_scale=True)'  (Strategy() args)
    --proof   'by sorry'                       (default; fill in later)
    --dry-run                                  (print without writing)

After scaffold, fill in the proof body in the .lean file and the
Strategy + spec body in the harness, then run:

    lake build Pythia.<Domain>.<Name>
    pytest tools/sim/<domain>_<name>.py

Once green, the theorem is on the same L0+L1 footing as everything
else in the manifest.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from textwrap import dedent
from typing import Sequence


REPO_ROOT = Path(__file__).resolve().parent.parent
PYTHIA_DIR = REPO_ROOT / "Pythia"
SIM_DIR = REPO_ROOT / "tools" / "sim"
MANIFEST_PATH = SIM_DIR / "theorem_manifest.py"


# ─────────────────────────────────────────────────────────────────────
# Templates
# ─────────────────────────────────────────────────────────────────────


_LEAN_TEMPLATE = dedent('''\
    /-
    Copyright (c) 2026 Pythia contributors. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.

    # {summary_title}

    {module_doc}

    ## Main results

    * `{name}` {summary}

    ## References
    {references_block}
    -/
    {imports_block}
    {opens_block}

    namespace {namespace}

    {definition_block}
    @[stat_lemma]
    {statement} := {proof}

    end {namespace}
''')


_HARNESS_TEMPLATE = dedent('''\
    """{module_doc_first}

    Lean side: `{namespace}.{name}` (file: {lean_path}).

    Empirical companion: PBT + sweep + mutation testing per the ATH-742
    sim runner. Fill in `STRATEGY` + the spec body, then verify with:

        python -m {module_dotted}
        pytest {sim_path}::{test_name}
    """
    from __future__ import annotations

    from tools.sim.harness import Mutation, Strategy, floats, isclose, run_harness


    def {spec_name}({spec_args}) -> bool:
        # TODO: implement the empirical equivalent of the Lean theorem.
        # Return True when the theorem holds at these parameter values
        # within rtol=1e-9.
        raise NotImplementedError(
            "fill in the spec body for {name}"
        )


    # TODO: tune the parameter ranges to match the theorem's domain.
    STRATEGY = Strategy(
        {strategy_lines}
    )

    # TODO: add 3 mutations that should fail on >= 5% of draws.
    # See tools/sim/mutations.py for reusable factories.
    MUTATIONS: tuple[Mutation, ...] = ()


    def main() -> int:
        result = run_harness(
            name="{harness_name}",
            spec={spec_name},
            strategy=STRATEGY,
            n_pbt=10_000,
            sweep_points=5,
            mutations=MUTATIONS,
        )
        print(result.summarize())
        return 0 if result.all_passed else 1


    def {test_name}() -> None:
        result = run_harness(
            name="{harness_name}",
            spec={spec_name},
            strategy=STRATEGY,
            n_pbt=2_000,
            sweep_points=4,
            mutations=MUTATIONS,
        )
        assert result.pbt_passed, (
            f"PBT failed at {{result.first_pbt_failure}}"
        )
        assert result.sweep_passed, (
            f"sweep failed at {{result.first_sweep_failure}}"
        )
        assert not result.mutations_missed, (
            f"vacuous-test risk: {{result.mutations_missed}}"
        )


    if __name__ == "__main__":
        import sys
        sys.exit(main())
''')


_MANIFEST_ENTRY_TEMPLATE = dedent('''\
        TheoremEntry(
            domain="{domain_lower}",
            name="{name}",
            lean_path="{lean_path}",
            lean_theorem="{namespace}.{name}",
            sim_path="{sim_path}",
            sim_test="{test_name}",
            mathlib_status="{mathlib_status}",
            summary="{summary}",
            references=[{references_csv}],
        ),
''')


# ─────────────────────────────────────────────────────────────────────
# Generation
# ─────────────────────────────────────────────────────────────────────


def _render_references(refs: Sequence[str]) -> str:
    if not refs:
        return ""
    return "\n" + "\n".join(f"    * {r}" for r in refs)


def _references_csv(refs: Sequence[str]) -> str:
    if not refs:
        return ""
    return ", ".join(f'"{r}"' for r in refs)


def _slugify(name: str) -> str:
    """Convert lean-style snake_case to a filesystem-safe slug."""
    slug = re.sub(r"[^A-Za-z0-9_]+", "_", name).strip("_")
    return slug.lower()


def _camel(name: str) -> str:
    """snake_case_name → SnakeCaseName."""
    return "".join(part.capitalize() for part in name.split("_"))


def render_lean_file(
    domain: str,
    name: str,
    statement: str,
    summary: str,
    imports: Sequence[str],
    opens: Sequence[str],
    references: Sequence[str],
    proof: str,
    definition: str = "",
) -> str:
    namespace = f"Pythia.{domain}"
    imports_block = "\n".join(f"import {i}" for i in imports)
    opens_block = "\n".join(f"open {o}" for o in opens) if opens else ""
    refs_block = _render_references(references) or "\n    (none)"
    return _LEAN_TEMPLATE.format(
        summary_title=summary or name.replace("_", " ").title(),
        module_doc=summary or "",
        name=name,
        summary=f"— {summary}" if summary else "",
        references_block=refs_block,
        imports_block=imports_block,
        opens_block=opens_block,
        namespace=namespace,
        definition_block=(definition + "\n") if definition else "",
        statement=statement,
        proof=proof,
    )


def render_harness_file(
    domain: str,
    name: str,
    summary: str,
    lean_path: str,
    sim_path: str,
    strategy_args: str,
    spec_args: str = "",
) -> str:
    domain_lower = domain.lower()
    namespace = f"Pythia.{domain}"
    spec_name = f"{name}_spec"
    test_name = f"test_{name}"
    harness_name = f"{domain_lower}.{name}"
    module_dotted = sim_path.replace("/", ".").removesuffix(".py")
    strategy_lines = ",\n        ".join(
        s.strip() for s in strategy_args.split(",") if s.strip()
    ) or "# TODO: name=floats(lo, hi),"
    return _HARNESS_TEMPLATE.format(
        module_doc_first=summary or f"Empirical companion for {namespace}.{name}.",
        namespace=namespace,
        name=name,
        lean_path=lean_path,
        module_dotted=module_dotted,
        sim_path=sim_path,
        test_name=test_name,
        spec_name=spec_name,
        spec_args=spec_args or "**kwargs",
        strategy_lines=strategy_lines,
        harness_name=harness_name,
    )


def render_manifest_entry(
    domain: str,
    name: str,
    summary: str,
    lean_path: str,
    sim_path: str,
    test_name: str,
    mathlib_status: str,
    references: Sequence[str],
) -> str:
    return _MANIFEST_ENTRY_TEMPLATE.format(
        domain_lower=domain.lower(),
        name=name,
        lean_path=lean_path,
        namespace=f"Pythia.{domain}",
        sim_path=sim_path,
        test_name=test_name,
        mathlib_status=mathlib_status,
        summary=summary.replace('"', '\\"'),
        references_csv=_references_csv(references),
    )


# ─────────────────────────────────────────────────────────────────────
# Manifest patching
# ─────────────────────────────────────────────────────────────────────


def _append_to_manifest(entry: str) -> bool:
    """Insert the new entry just before the closing `)` of MANIFEST.
    Returns True on a successful patch.
    """
    manifest_text = MANIFEST_PATH.read_text()
    # The manifest closes with a ) at the end of its trailing comma list.
    # Locate the LAST `)` that closes the `MANIFEST: tuple[...] = (`
    # block. Heuristic: find the unique line that is exactly `)\n`
    # following all the entries.
    lines = manifest_text.splitlines(keepends=True)
    insert_at = None
    for idx in range(len(lines) - 1, -1, -1):
        if lines[idx].rstrip() == ")":
            insert_at = idx
            break
    if insert_at is None:
        return False
    new_lines = (
        lines[:insert_at]
        + [entry]
        + lines[insert_at:]
    )
    MANIFEST_PATH.write_text("".join(new_lines))
    return True


# ─────────────────────────────────────────────────────────────────────
# CLI
# ─────────────────────────────────────────────────────────────────────


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--domain", required=True,
                   help="Capitalized domain folder, e.g. Economics, Bio, OR")
    p.add_argument("--name", required=True,
                   help="snake_case theorem name, e.g. solow_steady_state_pos")
    p.add_argument("--statement", required=True,
                   help="Full Lean theorem statement up to (but not including) the proof body")
    p.add_argument("--summary", default="",
                   help="One-sentence customer-facing description")
    p.add_argument("--imports", default="Mathlib,Pythia.Tactic.Pythia",
                   help="Comma-separated Lean imports")
    p.add_argument("--opens", default="",
                   help="Comma-separated `open` lines (e.g. Real)")
    p.add_argument("--reference", action="append", default=[],
                   help="Bibliographic reference (repeatable)")
    p.add_argument("--strategy", default="",
                   help="Comma-separated Strategy keyword args, e.g. 'k=floats(0.01,1e3,log_scale=True),x=floats(0,1)'")
    p.add_argument("--proof", default="by sorry",
                   help="Initial proof body. Default `by sorry` (fill in later)")
    p.add_argument("--mathlib-status", default="novel",
                   choices=["novel", "retag", "extension"])
    p.add_argument("--definition", default="",
                   help="Optional preceding `def` / `noncomputable def` block")
    p.add_argument("--dry-run", action="store_true",
                   help="Print rendered files instead of writing")
    args = p.parse_args(argv)

    domain = args.domain
    name = args.name
    name_camel = _camel(name)
    domain_lower = domain.lower()

    lean_path = f"Pythia/{domain}/{name_camel}.lean"
    sim_path = f"tools/sim/{domain_lower}_{_slugify(name)}.py"
    test_name = f"test_{name}"

    lean_src = render_lean_file(
        domain=domain,
        name=name,
        statement=args.statement,
        summary=args.summary,
        imports=[s.strip() for s in args.imports.split(",") if s.strip()],
        opens=[s.strip() for s in args.opens.split(",") if s.strip()],
        references=args.reference,
        proof=args.proof,
        definition=args.definition,
    )
    harness_src = render_harness_file(
        domain=domain,
        name=name,
        summary=args.summary,
        lean_path=lean_path,
        sim_path=sim_path,
        strategy_args=args.strategy,
    )
    manifest_entry = render_manifest_entry(
        domain=domain,
        name=name,
        summary=args.summary,
        lean_path=lean_path,
        sim_path=sim_path,
        test_name=test_name,
        mathlib_status=args.mathlib_status,
        references=args.reference,
    )

    if args.dry_run:
        print(f"--- {lean_path} ---\n{lean_src}")
        print(f"--- {sim_path} ---\n{harness_src}")
        print(f"--- manifest entry ---\n{manifest_entry}")
        return 0

    # Write files. Refuse to overwrite existing.
    lean_full = REPO_ROOT / lean_path
    sim_full = REPO_ROOT / sim_path
    if lean_full.exists():
        print(f"refused: {lean_path} already exists", file=sys.stderr)
        return 1
    if sim_full.exists():
        print(f"refused: {sim_path} already exists", file=sys.stderr)
        return 1
    lean_full.parent.mkdir(parents=True, exist_ok=True)
    sim_full.parent.mkdir(parents=True, exist_ok=True)
    lean_full.write_text(lean_src)
    sim_full.write_text(harness_src)
    if not _append_to_manifest(manifest_entry):
        print(
            "wrote files but could not patch manifest; insert this "
            f"entry manually into {MANIFEST_PATH}:\n{manifest_entry}",
            file=sys.stderr,
        )
        return 2
    print(f"✓ wrote {lean_path}")
    print(f"✓ wrote {sim_path}")
    print(f"✓ patched {MANIFEST_PATH}")
    print()
    print(f"next steps:")
    print(f"  1. fill in the proof body in {lean_path}")
    print(f"  2. fill in STRATEGY + spec body + MUTATIONS in {sim_path}")
    print(f"  3. lake build Pythia.{domain}.{name_camel}")
    print(f"  4. pytest {sim_path}::{test_name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
