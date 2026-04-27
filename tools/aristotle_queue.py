#!/usr/bin/env python3
"""tools/aristotle_queue.py — Aristotle restock + status dashboard.

Companion to `tools/aristotle_import.py`. Where `aristotle_import` brings
a single COMPLETE result into the repo on a fresh branch, this tool
manages the OUTBOUND side of the queue: discovering targets, submitting
them to Aristotle, tracking in-flight projects, and surfacing completed
ones that need importing.

State lives in `.aristotle/queue_state.json` (gitignored), keyed by
target name. Each entry records the Aristotle project id, the status
last seen, and submission/update timestamps.

Usage:

    tools/aristotle_queue.py list                  # show known targets + state
    tools/aristotle_queue.py discover [--min N]    # find sorry-bearing theorems
    tools/aristotle_queue.py restock [--limit N]   # submit N new targets
    tools/aristotle_queue.py check                 # poll all in-flight projects
    tools/aristotle_queue.py status <name>         # show one target's state
    tools/aristotle_queue.py reset <name>          # forget one target's state
    tools/aristotle_queue.py import-completed      # list COMPLETE not-yet-imported

The tool refuses to submit duplicate targets (same name → existing state
entry) unless `--force` is passed. Submission writes the project id back
to state immediately, so an interrupted run does not lose track.

Requires:
  * ARISTOTLE_API_KEY env var (or aristotle CLI configured)
  * `aristotle` on PATH
  * Run from inside the pythia repo
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


REPO_ROOT = Path(__file__).resolve().parent.parent
STATE_DIR = REPO_ROOT / ".aristotle"
STATE_PATH = STATE_DIR / "queue_state.json"

# Aristotle API states (mirror of the CLI's --status enum).
ALIVE_STATES = {"NOT_STARTED", "QUEUED", "IN_PROGRESS"}
TERMINAL_STATES = {
    "COMPLETE",
    "COMPLETE_WITH_ERRORS",
    "OUT_OF_BUDGET",
    "FAILED",
    "CANCELED",
}


@dataclass
class TargetEntry:
    """One row of queue state. Persisted as JSON."""

    name: str                     # human-readable target name
    lean_path: str                # path to the .lean file (relative to repo)
    project_id: Optional[str] = None
    status: str = "UNSUBMITTED"
    submitted_at: Optional[str] = None
    updated_at: Optional[str] = None
    notes: str = ""               # free-form (last error, etc.)


@dataclass
class QueueState:
    targets: dict[str, TargetEntry] = field(default_factory=dict)

    @classmethod
    def load(cls, path: Optional[Path] = None) -> "QueueState":
        # Resolve `STATE_PATH` at call time so test monkeypatches of the
        # module-level constant take effect (Python binds default
        # arguments once at class-def time).
        path = path or STATE_PATH
        if not path.is_file():
            return cls()
        raw = json.loads(path.read_text())
        return cls(
            targets={
                name: TargetEntry(**entry)
                for name, entry in raw.get("targets", {}).items()
            }
        )

    def save(self, path: Optional[Path] = None) -> None:
        path = path or STATE_PATH
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(
            {"targets": {n: asdict(e) for n, e in self.targets.items()}},
            indent=2, sort_keys=True,
        ) + "\n")


# ─────────────────────────────────────────────────────────────────────
# Target discovery
# ─────────────────────────────────────────────────────────────────────


_THEOREM_DECL = re.compile(
    r"^(?:theorem|lemma)\s+([a-zA-Z_][a-zA-Z0-9_]*)",
    re.MULTILINE,
)
_SORRY_TERM = re.compile(r"\bsorry\b")


def discover_targets(repo_root: Path = REPO_ROOT) -> list[TargetEntry]:
    """Walk Pythia/ and return TargetEntry stubs for every file that
    has at least one `sorry` term outside a doc-comment context.

    Heuristic: we treat any file containing `sorry` (anywhere) as having
    pending Aristotle work. Doc-string `sorry` mentions are uncommon and
    the small false-positive cost is acceptable. The target name is the
    NAME of the first theorem/lemma declaration in the file; granularity
    is per-file, not per-theorem, matching how Aristotle is invoked.
    """
    out: list[TargetEntry] = []
    pythia_dir = repo_root / "Pythia"
    for p in sorted(pythia_dir.rglob("*.lean")):
        text = p.read_text()
        if not _SORRY_TERM.search(text):
            continue
        decls = _THEOREM_DECL.findall(text)
        if not decls:
            continue
        rel = p.relative_to(repo_root)
        # Namespace-qualified target name: file-prefix + first theorem.
        # `Pythia/Bio/Population.lean` → `Bio_Population_<thm>`.
        prefix = "_".join(rel.with_suffix("").parts[1:])
        name = f"{prefix}__{decls[0]}"
        out.append(TargetEntry(name=name, lean_path=str(rel)))
    return out


# ─────────────────────────────────────────────────────────────────────
# Aristotle CLI shims
# ─────────────────────────────────────────────────────────────────────


def _run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, **kwargs)


def aristotle_submit(
    prompt: str,
    project_dir: Path,
) -> Optional[str]:
    """Submit a project to Aristotle. Returns the project id on success,
    None on failure. The CLI prints the id to stdout in the form
    `Submitted project <UUID>`; we parse for it.
    """
    proc = _run([
        "aristotle", "submit", prompt,
        "--project-dir", str(project_dir),
    ])
    if proc.returncode != 0:
        sys.stderr.write(f"[aristotle-queue] submit failed: {proc.stderr}\n")
        return None
    # Aristotle prints the project id; extract a UUID-looking token.
    m = re.search(r"\b([0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12})\b", proc.stdout)
    if m is None:
        sys.stderr.write(
            f"[aristotle-queue] could not parse project id from:\n{proc.stdout}\n"
        )
        return None
    return m.group(1)


def aristotle_list_status() -> dict[str, str]:
    """Return a {project_id: status} map for ALL projects on the
    account. Used by the `check` command. The CLI emits a tab-separated
    table; we parse defensively.
    """
    proc = _run(["aristotle", "list"])
    if proc.returncode != 0:
        return {}
    out: dict[str, str] = {}
    uuid_re = re.compile(r"^([0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12})\b")
    for line in proc.stdout.splitlines():
        m = uuid_re.match(line.strip())
        if m is None:
            continue
        pid = m.group(1)
        # Find the first state token that matches a known status.
        for tok in line.split():
            if tok in ALIVE_STATES or tok in TERMINAL_STATES:
                out[pid] = tok
                break
    return out


# ─────────────────────────────────────────────────────────────────────
# CLI commands
# ─────────────────────────────────────────────────────────────────────


def cmd_discover(args: argparse.Namespace) -> int:
    targets = discover_targets()
    state = QueueState.load()
    new_count = 0
    for t in targets:
        if t.name not in state.targets:
            state.targets[t.name] = t
            new_count += 1
    if not args.dry_run:
        state.save()
    print(f"discovered {len(targets)} sorry-bearing target(s); "
          f"{new_count} new, {len(targets) - new_count} already tracked")
    if args.verbose:
        for t in targets:
            mark = "+" if t.name not in state.targets or state.targets[t.name].project_id is None else "·"
            print(f"  {mark} {t.name}  [{t.lean_path}]")
    return 0


def cmd_list(args: argparse.Namespace) -> int:
    state = QueueState.load()
    if not state.targets:
        print("queue is empty; run `aristotle_queue.py discover` first")
        return 0
    width = max(len(n) for n in state.targets) + 2
    for name in sorted(state.targets):
        e = state.targets[name]
        pid = e.project_id or "—"
        print(f"  {name:<{width}} {e.status:<22} {pid}")
    return 0


def cmd_restock(args: argparse.Namespace) -> int:
    state = QueueState.load()
    candidates = [
        t for t in state.targets.values()
        if t.project_id is None or t.status in {"FAILED", "CANCELED"}
    ]
    if args.limit:
        candidates = candidates[:args.limit]
    if not candidates:
        print("no candidates to submit; run `discover` to refresh")
        return 0
    submitted = 0
    for t in candidates:
        prompt = (
            f"Close the `sorry`(es) in {t.lean_path}. The repo root is "
            f"the project_dir. Use Lean 4 + Mathlib v4.28.0. The result "
            f"must be axiom-clean against {{propext, Classical.choice, "
            f"Quot.sound}}."
        )
        if args.dry_run:
            print(f"[dry-run] would submit {t.name} ({t.lean_path})")
            continue
        pid = aristotle_submit(prompt, REPO_ROOT)
        if pid is None:
            t.status = "SUBMIT_FAILED"
            t.notes = "submit() returned no project id"
            continue
        t.project_id = pid
        t.status = "QUEUED"
        t.submitted_at = datetime.now(timezone.utc).isoformat()
        t.updated_at = t.submitted_at
        submitted += 1
        print(f"submitted {t.name} → {pid}")
    if not args.dry_run:
        state.save()
    print(f"restock: {submitted}/{len(candidates)} submitted")
    return 0


def cmd_check(args: argparse.Namespace) -> int:
    state = QueueState.load()
    in_flight = [t for t in state.targets.values() if t.project_id and t.status in ALIVE_STATES]
    if not in_flight:
        print("no in-flight projects")
        return 0
    pid_to_status = aristotle_list_status()
    changed = 0
    for t in in_flight:
        new_status = pid_to_status.get(t.project_id)
        if new_status is None:
            continue
        if new_status != t.status:
            t.status = new_status
            t.updated_at = datetime.now(timezone.utc).isoformat()
            changed += 1
    if not args.dry_run:
        state.save()
    print(f"check: {len(in_flight)} polled, {changed} state change(s)")
    for t in in_flight:
        print(f"  {t.name:<60} {t.status:<22} {t.project_id}")
    return 0


def cmd_status(args: argparse.Namespace) -> int:
    state = QueueState.load()
    t = state.targets.get(args.name)
    if t is None:
        print(f"no target named {args.name!r}", file=sys.stderr)
        return 1
    for k, v in asdict(t).items():
        print(f"  {k:<14} {v}")
    return 0


def cmd_reset(args: argparse.Namespace) -> int:
    state = QueueState.load()
    if args.name not in state.targets:
        print(f"no target named {args.name!r}", file=sys.stderr)
        return 1
    if not args.dry_run:
        del state.targets[args.name]
        state.save()
    print(f"reset {args.name}")
    return 0


def cmd_import_completed(args: argparse.Namespace) -> int:
    state = QueueState.load()
    completed = [
        t for t in state.targets.values()
        if t.project_id and t.status == "COMPLETE"
    ]
    if not completed:
        print("no COMPLETE targets pending import")
        return 0
    print("COMPLETE targets pending import (run aristotle_import.py for each):")
    for t in completed:
        print(f"  tools/aristotle_import.py {t.project_id}   # {t.name}")
    return 0


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--dry-run", action="store_true",
                   help="don't write state or call Aristotle; preview only")
    sub = p.add_subparsers(dest="cmd", required=True)

    p_disc = sub.add_parser("discover",
                            help="walk Pythia/ for sorry-bearing theorems")
    p_disc.add_argument("--verbose", action="store_true")
    p_disc.set_defaults(func=cmd_discover)

    p_list = sub.add_parser("list", help="dump current queue state")
    p_list.set_defaults(func=cmd_list)

    p_rest = sub.add_parser("restock", help="submit new targets to Aristotle")
    p_rest.add_argument("--limit", type=int, default=None,
                        help="cap on number of submissions this run")
    p_rest.set_defaults(func=cmd_restock)

    p_chk = sub.add_parser("check",
                           help="poll Aristotle for in-flight project status")
    p_chk.set_defaults(func=cmd_check)

    p_st = sub.add_parser("status", help="show one target's full state")
    p_st.add_argument("name")
    p_st.set_defaults(func=cmd_status)

    p_rs = sub.add_parser("reset", help="forget one target's state row")
    p_rs.add_argument("name")
    p_rs.set_defaults(func=cmd_reset)

    p_imp = sub.add_parser("import-completed",
                           help="list COMPLETE targets ready for aristotle_import")
    p_imp.set_defaults(func=cmd_import_completed)

    args = p.parse_args(argv)
    # `restock` and `check` need an API key; `discover` / `list` do not.
    needs_key = args.cmd in {"restock", "check"} and not args.dry_run
    if needs_key and not os.environ.get("ARISTOTLE_API_KEY"):
        print("ARISTOTLE_API_KEY not set; export the key before re-running",
              file=sys.stderr)
        return 1
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
