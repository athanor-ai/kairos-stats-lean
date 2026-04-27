#!/usr/bin/env python3
"""tools/aristotle_import.py — bring an Aristotle result into pythia.

Aristotle (harmonic.fun) closes hard Lean theorems we couldn't close in
the in-repo cycle engine. The CLI submits projects, polls until COMPLETE,
and downloads a tarball with the modified Lean files. This script
inspects an Aristotle result against the current pythia main, identifies
new / changed `.lean` files, and stages them on a fresh branch ready for
review. We do NOT auto-merge — every formal-proof addition gets a human
look (axiom audit, vacuous-truth scan, scope sanity).

Usage:

    tools/aristotle_import.py <project_id> [--branch <name>] [--dry-run]

Examples:

    # See what changed; don't touch the working tree
    tools/aristotle_import.py ff404663 --dry-run

    # Stage the import on a fresh branch
    tools/aristotle_import.py ff404663 --branch research/aristotle-bdg-import

    # Default branch name = research/aristotle-<short-id>
    tools/aristotle_import.py ff404663

The script:
  1. `aristotle result <id>` → tarball at /tmp/aristotle_results/<id>
  2. Untar to a working directory
  3. Diff against the current pythia main: list new + modified .lean files
  4. Print summary (file paths, byte counts, head of ARISTOTLE_SUMMARY.md
     when present)
  5. Unless --dry-run, copy new + modified .lean files into the pythia
     repo on a fresh branch + run `lake build` against each new module +
     stage a commit. The user reviews + opens the PR.

Requires:
  * ARISTOTLE_API_KEY env var (or aristotle CLI configured)
  * lake on PATH (for the build sanity check)
  * Run from inside the pythia repo
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path
from typing import Optional


REPO_ROOT = Path(__file__).resolve().parent.parent


def _run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    """Run a command, capturing output. Returns the CompletedProcess
    so callers can inspect rc + stdout + stderr without raising."""
    return subprocess.run(cmd, capture_output=True, text=True, **kwargs)


def _aristotle_download(project_id: str, dest_dir: Path) -> Path:
    """Run `aristotle result <id> --destination <path>`. The CLI saves
    the tarball at the destination path (NOT inside it as a directory).
    Returns the tarball path.
    """
    dest_dir.mkdir(parents=True, exist_ok=True)
    tarball = dest_dir / project_id
    if tarball.exists():
        print(f"[aristotle-import] reusing cached tarball {tarball}")
        return tarball
    print(f"[aristotle-import] aristotle result {project_id} ...")
    proc = _run([
        "aristotle", "result", project_id,
        "--destination", str(tarball),
    ])
    if proc.returncode != 0:
        print(proc.stdout)
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError(
            f"aristotle result {project_id} failed (rc={proc.returncode})"
        )
    return tarball


def _untar(tarball: Path, dest: Path) -> Path:
    """Extract `tarball` into `dest`. Returns the extracted root
    directory (typically `dest/<tarball.stem>` or one of the tar's
    top-level entries).
    """
    if dest.exists():
        shutil.rmtree(dest)
    dest.mkdir(parents=True)
    with tarfile.open(tarball, "r:gz") as t:
        t.extractall(dest)
    # Most Aristotle tarballs contain a single top-level dir; locate
    # it via the lakefile.
    candidates = list(dest.glob("*/lakefile.lean"))
    if not candidates:
        raise RuntimeError(
            f"tarball at {tarball} has no lakefile.lean (Aristotle "
            f"tarballs always do); listing root: "
            f"{[p.name for p in dest.iterdir()]}"
        )
    return candidates[0].parent


def _list_lean_files(root: Path) -> list[Path]:
    """All `.lean` files under `root/Pythia/`, relative to `root`."""
    pythia_dir = root / "Pythia"
    if not pythia_dir.is_dir():
        return []
    return sorted(p.relative_to(root) for p in pythia_dir.rglob("*.lean"))


def _diff_against_main(
    aristotle_root: Path,
) -> tuple[list[Path], list[Path], list[Path]]:
    """Return (new_files, modified_files, unchanged_files) where each
    path is relative to repo root and points at a `.lean` file under
    `Pythia/`.
    """
    new: list[Path] = []
    modified: list[Path] = []
    unchanged: list[Path] = []
    for rel in _list_lean_files(aristotle_root):
        aristotle_file = aristotle_root / rel
        repo_file = REPO_ROOT / rel
        if not repo_file.exists():
            new.append(rel)
            continue
        # Compare bytes; trailing-newline differences count as modified.
        if aristotle_file.read_bytes() != repo_file.read_bytes():
            modified.append(rel)
        else:
            unchanged.append(rel)
    return new, modified, unchanged


def _read_summary(aristotle_root: Path, max_lines: int = 30) -> Optional[str]:
    """Read the first `max_lines` lines of ARISTOTLE_SUMMARY.md if
    present. None when missing.
    """
    summary = aristotle_root / "ARISTOTLE_SUMMARY.md"
    if not summary.is_file():
        return None
    lines = summary.read_text().splitlines()
    return "\n".join(lines[:max_lines])


def _print_diff_report(
    project_id: str,
    summary: Optional[str],
    new: list[Path],
    modified: list[Path],
    unchanged: list[Path],
) -> None:
    print(f"\n=== Aristotle result {project_id} ===")
    if summary:
        print("\n--- ARISTOTLE_SUMMARY.md (first 30 lines) ---")
        print(summary)
    print(f"\n--- diff vs pythia main ---")
    print(f"new files     : {len(new)}")
    for p in new:
        size = (REPO_ROOT.parent / p).stat().st_size if False else None
        print(f"  + {p}")
    print(f"modified files: {len(modified)}")
    for p in modified:
        print(f"  ~ {p}")
    print(f"unchanged     : {len(unchanged)}")


def _stage_branch(
    branch_name: str,
    aristotle_root: Path,
    new: list[Path],
    modified: list[Path],
) -> None:
    """Create branch `branch_name` off main, copy new + modified files,
    update the Pythia umbrella import, run `lake build` on each new
    module, and leave the branch staged for the user to review + push.
    """
    # Verify clean working tree before branching.
    proc = _run(["git", "-C", str(REPO_ROOT), "status", "--porcelain"])
    if proc.stdout.strip():
        raise RuntimeError(
            "working tree not clean; commit or stash before importing"
        )
    proc = _run(["git", "-C", str(REPO_ROOT), "checkout", "main"])
    if proc.returncode != 0:
        raise RuntimeError(f"checkout main failed: {proc.stderr}")
    proc = _run(["git", "-C", str(REPO_ROOT), "pull", "origin", "main"])
    if proc.returncode != 0:
        print(f"[aristotle-import] warning: pull main failed: {proc.stderr}")
    proc = _run([
        "git", "-C", str(REPO_ROOT), "checkout", "-b", branch_name,
    ])
    if proc.returncode != 0:
        raise RuntimeError(f"checkout -b {branch_name} failed: {proc.stderr}")

    # Copy new + modified files.
    for rel in new + modified:
        src = aristotle_root / rel
        dst = REPO_ROOT / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        print(f"[aristotle-import] copied {rel}")

    # Update Pythia.lean umbrella with `import` lines for any new
    # top-level Pythia modules.
    umbrella = REPO_ROOT / "Pythia.lean"
    if umbrella.is_file() and new:
        existing = umbrella.read_text()
        added: list[str] = []
        for rel in new:
            # Pythia/Foo.lean → import Pythia.Foo
            mod = ".".join(rel.with_suffix("").parts)
            if not mod.startswith("Pythia."):
                continue
            line = f"import {mod}\n"
            if line not in existing:
                added.append(line)
        if added:
            umbrella.write_text(existing.rstrip() + "\n" + "".join(added))
            print(
                f"[aristotle-import] added {len(added)} imports to Pythia.lean"
            )

    # Sanity: lake build the new modules. Only checks build-clean; the
    # axiom audit fires separately on PR via CI.
    for rel in new:
        if not str(rel).startswith("Pythia/") or rel.suffix != ".lean":
            continue
        mod = ".".join(rel.with_suffix("").parts)
        print(f"[aristotle-import] lake build {mod} ...")
        proc = _run([
            "lake", "build", mod,
        ], cwd=REPO_ROOT)
        if proc.returncode != 0:
            print(proc.stdout)
            print(proc.stderr, file=sys.stderr)
            print(
                f"[aristotle-import] WARN: lake build failed for {mod}; "
                f"branch staged anyway for human review",
                file=sys.stderr,
            )

    print(
        f"\n[aristotle-import] DONE\n"
        f"  branch: {branch_name}\n"
        f"  next steps:\n"
        f"    1. cd {REPO_ROOT}\n"
        f"    2. git status                       # review what was copied\n"
        f"    3. (review the new .lean files for vacuous-truth, sorry, banned constructs)\n"
        f"    4. (optionally add tools/sim/<domain>_<theorem>.py harness companion)\n"
        f"    5. git add . && git commit -m 'feat(...): import Aristotle result <id>'\n"
        f"    6. git push origin {branch_name}\n"
        f"    7. gh pr create\n"
    )


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("project_id", help="Aristotle project UUID (or 8-char prefix)")
    p.add_argument("--branch", default=None,
                   help="Git branch name to stage on (default: research/aristotle-<short-id>)")
    p.add_argument("--dry-run", action="store_true",
                   help="Print diff report only; don't touch the working tree")
    p.add_argument("--results-dir", default="/tmp/aristotle_results",
                   help="Where to cache + extract Aristotle tarballs")
    args = p.parse_args(argv)

    if not os.environ.get("ARISTOTLE_API_KEY"):
        print(
            "ARISTOTLE_API_KEY not set; "
            "source ~/.bashrc or export the key before re-running",
            file=sys.stderr,
        )
        return 1

    project_id = args.project_id
    short = project_id.split("-")[0][:8]
    branch_name = args.branch or f"research/aristotle-{short}"
    results_dir = Path(args.results_dir)
    work_dir = results_dir / f"{short}-extracted"

    try:
        tarball = _aristotle_download(project_id, results_dir)
        aristotle_root = _untar(tarball, work_dir)
        new, modified, unchanged = _diff_against_main(aristotle_root)
        summary = _read_summary(aristotle_root)
        _print_diff_report(project_id, summary, new, modified, unchanged)

        if args.dry_run:
            print("\n[aristotle-import] dry-run: no files copied")
            return 0
        if not (new or modified):
            print("\n[aristotle-import] nothing to import; skipping branch creation")
            return 0
        _stage_branch(branch_name, aristotle_root, new, modified)
        return 0
    except Exception as e:
        print(f"[aristotle-import] ERROR: {type(e).__name__}: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
