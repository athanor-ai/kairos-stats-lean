#!/usr/bin/env python3
"""tools/run_pythia_sim.py — full empirical sweep across the manifest.

Executes ``pytest`` against every theorem registered in
``tools.sim.theorem_manifest.MANIFEST``. Used as a CI gate (see
.github/workflows/) and locally via:

    python3 tools/run_pythia_sim.py [pytest-extra-args...]

By default runs every harness with the small (n_pbt=2_000) `test_*`
hook each module exposes. Pass `--full` to invoke each module's
`main()` (n_pbt=10_000) instead — slower but matches what subagents
report on PR.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

# Add the repo root to sys.path so we can `from tools.sim...` even
# when invoked as `tools/run_pythia_sim.py` (rather than as a module).
_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from tools.sim.theorem_manifest import (  # noqa: E402
    MANIFEST,
    assert_files_exist,
    pytest_args,
)


def _run_pytest(extra: list[str]) -> int:
    args = [sys.executable, "-m", "pytest", *pytest_args(), *extra]
    print("[run_pythia_sim] " + " ".join(args), flush=True)
    return subprocess.call(args)


def _run_full() -> int:
    """Invoke each harness's main() one at a time. Exit on first
    failure."""
    rc_total = 0
    for entry in MANIFEST:
        module = entry.sim_path.replace("/", ".").removesuffix(".py")
        print(f"\n[run_pythia_sim] full → {module}", flush=True)
        rc = subprocess.call([sys.executable, "-m", module])
        if rc != 0:
            print(f"[run_pythia_sim] FAILED: {module} (rc={rc})", file=sys.stderr)
            rc_total = rc
    return rc_total


def main(argv: list[str] | None = None) -> int:
    args = list(argv if argv is not None else sys.argv[1:])
    missing = assert_files_exist()
    if missing:
        print("[run_pythia_sim] manifest references missing files:",
              file=sys.stderr)
        for m in missing:
            print(f"  - {m}", file=sys.stderr)
        return 1

    if "--full" in args:
        args.remove("--full")
        if args:
            print("[run_pythia_sim] --full takes no extra args; ignoring", file=sys.stderr)
        return _run_full()
    return _run_pytest(args)


if __name__ == "__main__":
    sys.exit(main())
