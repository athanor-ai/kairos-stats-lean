#!/usr/bin/env python3
"""Pythia theorem index — retrieval-augmented proving backend.

Indexes all proved (sorry-free) theorems from the Pythia Lean library
into a SQLite database with FTS5 full-text search on theorem names,
types, and module paths. Agents query the index via
`kairos.lean_retrieve(goal)` to get the 5-15 most relevant lemmas for
a proof target, then `kairos.lean_scaffold(goal, retrieved)` assembles
a minimal .lean file with exactly those imports.

Usage:
    python3 tools/theorem_index.py build     # (re)build the index
    python3 tools/theorem_index.py search "sub-Gaussian martingale"
    python3 tools/theorem_index.py search "mod 2^n overflow"
    python3 tools/theorem_index.py stats     # index statistics
"""
from __future__ import annotations

import argparse
import os
import re
import sqlite3
import sys
from pathlib import Path

PYTHIA_ROOT = Path(__file__).resolve().parent.parent
DB_PATH = PYTHIA_ROOT / ".pythia" / "theorem_index.db"
LEAN_DIR = PYTHIA_ROOT / "Pythia"


def _extract_theorems(lean_dir: Path) -> list[dict]:
    """Walk .lean files, extract theorem/lemma declarations with
    their type signatures, sorry status, and domain tags."""
    results = []
    for lean_file in sorted(lean_dir.rglob("*.lean")):
        if "Scratch" in str(lean_file) or ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(PYTHIA_ROOT)
        module = str(rel).replace("/", ".").removesuffix(".lean")

        # Infer domain tag from path
        parts = rel.parts
        if len(parts) >= 2:
            domain = parts[1]  # Pythia/<Domain>/...
        else:
            domain = "core"

        try:
            lines = lean_file.read_text(errors="replace").splitlines()
        except OSError:
            continue

        i = 0
        while i < len(lines):
            line = lines[i]
            m = re.match(
                r"^(theorem|lemma|noncomputable def|noncomputable instance|def|instance)\s+(\S+)",
                line,
            )
            if m:
                kind = m.group(1)
                name = m.group(2)
                # Grab the full signature (up to `:= by` or `:=`)
                sig_lines = [line]
                j = i + 1
                while j < min(i + 30, len(lines)):
                    sig_lines.append(lines[j])
                    if ":= by" in lines[j] or ":=" in lines[j] and "sorry" not in lines[j]:
                        break
                    if "sorry" in lines[j]:
                        break
                    j += 1
                sig = " ".join(l.strip() for l in sig_lines)

                # Check sorry in the proof body (next ~30 lines)
                body_window = "\n".join(lines[i : min(i + 40, len(lines))])
                has_sorry = "sorry" in body_window and kind in ("theorem", "lemma")

                # Domain tags from keywords in the signature
                tags = {domain.lower()}
                sig_lower = sig.lower()
                for kw, tag in [
                    ("measure", "probability"), ("martingale", "probability"),
                    ("subgaussian", "probability"), ("gaussian", "probability"),
                    ("exp", "analysis"), ("log", "analysis"),
                    ("bitvec", "hardware"), ("mod", "hardware"),
                    ("fifo", "hardware"), ("gray", "hardware"),
                    ("mtbf", "hardware"), ("synchronizer", "hardware"),
                    ("ieee", "hardware"), ("float", "hardware"),
                    ("hamming", "coding"), ("ecc", "coding"),
                    ("induction", "verification"), ("bmc", "verification"),
                    ("sandwich", "verification"), ("oracle", "verification"),
                    ("trace", "verification"), ("wellformed", "verification"),
                    ("eta", "quantization"), ("slack", "quantization"),
                    ("quantize", "quantization"),
                ]:
                    if kw in sig_lower:
                        tags.add(tag)

                results.append({
                    "module": module,
                    "name": name,
                    "kind": kind,
                    "signature": sig[:500],
                    "line": i + 1,
                    "file": str(rel),
                    "domain": domain.lower(),
                    "tags": ",".join(sorted(tags)),
                    "has_sorry": has_sorry,
                    "proved": not has_sorry,
                })
            i += 1

    return results


def build_index() -> None:
    """(Re)build the theorem index from Lean source."""
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    if DB_PATH.exists():
        DB_PATH.unlink()

    conn = sqlite3.connect(str(DB_PATH))
    conn.execute("""
        CREATE TABLE theorems (
            id INTEGER PRIMARY KEY,
            module TEXT NOT NULL,
            name TEXT NOT NULL,
            kind TEXT NOT NULL,
            signature TEXT NOT NULL,
            line INTEGER NOT NULL,
            file TEXT NOT NULL,
            domain TEXT NOT NULL,
            tags TEXT NOT NULL,
            has_sorry BOOLEAN NOT NULL,
            proved BOOLEAN NOT NULL
        )
    """)
    # FTS5 for full-text search on name + signature + tags
    conn.execute("""
        CREATE VIRTUAL TABLE theorems_fts USING fts5(
            name, signature, tags, domain,
            content='theorems',
            content_rowid='id'
        )
    """)

    theorems = _extract_theorems(LEAN_DIR)
    for t in theorems:
        conn.execute(
            "INSERT INTO theorems (module, name, kind, signature, line, file, "
            "domain, tags, has_sorry, proved) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (t["module"], t["name"], t["kind"], t["signature"], t["line"],
             t["file"], t["domain"], t["tags"], t["has_sorry"], t["proved"]),
        )
    # Populate FTS
    conn.execute("""
        INSERT INTO theorems_fts (rowid, name, signature, tags, domain)
        SELECT id, name, signature, tags, domain FROM theorems
    """)

    conn.commit()
    proved = sum(1 for t in theorems if t["proved"])
    sorry = sum(1 for t in theorems if not t["proved"])
    print(f"Indexed {len(theorems)} declarations ({proved} proved, {sorry} sorry)")
    print(f"DB: {DB_PATH} ({DB_PATH.stat().st_size // 1024} KB)")

    # Domain breakdown
    domains: dict[str, int] = {}
    for t in theorems:
        if t["proved"]:
            domains[t["domain"]] = domains.get(t["domain"], 0) + 1
    print("\nProved by domain:")
    for d, c in sorted(domains.items(), key=lambda x: -x[1]):
        print(f"  {d:30s} {c}")

    conn.close()


def search(query: str, top_k: int = 15, proved_only: bool = True) -> list[dict]:
    """Search the theorem index by natural-language query."""
    if not DB_PATH.exists():
        print("Index not built. Run: python3 tools/theorem_index.py build",
              file=sys.stderr)
        return []

    conn = sqlite3.connect(str(DB_PATH))
    conn.row_factory = sqlite3.Row

    # FTS5 match query — tokenize on spaces, match any term
    fts_query = " OR ".join('"' + w + '"' if "-" in w else w for w in query.split())
    filter_clause = "AND t.proved = 1" if proved_only else ""

    rows = conn.execute(f"""
        SELECT t.*, rank
        FROM theorems_fts f
        JOIN theorems t ON f.rowid = t.id
        WHERE theorems_fts MATCH ?
        {filter_clause}
        ORDER BY rank
        LIMIT ?
    """, (fts_query, top_k)).fetchall()

    results = [dict(r) for r in rows]
    conn.close()
    return results


def scaffold(goal: str, retrieved: list[dict]) -> str:
    """Assemble a minimal .lean file with exactly the retrieved lemmas
    available as imports. The drafter fills in the proof."""
    # Collect unique modules needed
    modules = sorted(set(r["module"] for r in retrieved))

    lines = ["-- Auto-generated by Pythia theorem retrieval"]
    lines.append("-- Goal: " + goal[:200])
    lines.append("")
    lines.append("import Mathlib")
    for mod in modules:
        lines.append(f"import {mod}")
    lines.append("")
    lines.append("open MeasureTheory ProbabilityTheory Pythia")
    lines.append("")
    lines.append("-- Retrieved lemmas (ranked by relevance):")
    for r in retrieved:
        lines.append(f"-- {r['name']} ({r['module']}:{r['line']})")
        sig_short = r["signature"][:120].replace("\n", " ")
        lines.append(f"--   {sig_short}")
    lines.append("")
    lines.append(f"-- TODO: prove the goal using the above lemmas")
    lines.append(f"theorem target_goal := by")
    lines.append(f"  sorry")
    lines.append("")

    return "\n".join(lines)


def print_stats() -> None:
    """Print index statistics."""
    if not DB_PATH.exists():
        print("Index not built.")
        return
    conn = sqlite3.connect(str(DB_PATH))
    total = conn.execute("SELECT COUNT(*) FROM theorems").fetchone()[0]
    proved = conn.execute("SELECT COUNT(*) FROM theorems WHERE proved = 1").fetchone()[0]
    sorry = conn.execute("SELECT COUNT(*) FROM theorems WHERE proved = 0").fetchone()[0]

    print(f"Pythia theorem index: {total} declarations ({proved} proved, {sorry} sorry)")
    print(f"DB: {DB_PATH} ({DB_PATH.stat().st_size // 1024} KB)")
    print()

    rows = conn.execute("""
        SELECT domain, COUNT(*) as total,
               SUM(CASE WHEN proved THEN 1 ELSE 0 END) as proved_count
        FROM theorems GROUP BY domain ORDER BY total DESC
    """).fetchall()
    print(f"{'Domain':30s} {'Total':>6s} {'Proved':>7s} {'Sorry':>6s}")
    print("-" * 55)
    for r in rows:
        sorry_count = r[1] - r[2]
        print(f"{r[0]:30s} {r[1]:6d} {r[2]:7d} {sorry_count:6d}")
    conn.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Pythia theorem index")
    sub = parser.add_subparsers(dest="cmd")
    sub.add_parser("build", help="(Re)build the index from Lean source")
    sp_search = sub.add_parser("search", help="Search for relevant lemmas")
    sp_search.add_argument("query", help="Natural-language goal description")
    sp_search.add_argument("-k", "--top-k", type=int, default=10)
    sp_search.add_argument("--include-sorry", action="store_true")
    sub.add_parser("stats", help="Print index statistics")
    sp_scaffold = sub.add_parser("scaffold",
                                  help="Generate a minimal .lean file for a goal")
    sp_scaffold.add_argument("goal", help="Goal statement")

    args = parser.parse_args()
    if args.cmd == "build":
        build_index()
    elif args.cmd == "search":
        results = search(args.query, args.top_k,
                         proved_only=not args.include_sorry)
        if not results:
            print("No results.")
        for r in results:
            sorry_tag = " [SORRY]" if r["has_sorry"] else ""
            print(f"{r['name']:50s} {r['module']:40s} :{r['line']}{sorry_tag}")
            sig = r["signature"][:100].replace("\n", " ")
            print(f"  {sig}")
            print()
    elif args.cmd == "scaffold":
        retrieved = search(args.goal, top_k=10, proved_only=True)
        print(scaffold(args.goal, retrieved))
    elif args.cmd == "stats":
        print_stats()
    else:
        parser.print_help()
