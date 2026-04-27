"""Run an extracted Lean code block through ``lake env lean``.

Each block runs in a tempfile under the project's ``Pythia/Scratch/``
namespace so the running ``lake`` instance can find Mathlib + the
local Pythia modules. The tempfile is cleaned up after the run
regardless of outcome.

We deliberately do NOT cache the lake startup across calls because:

* Per-block startup is ~5s on a warm cache (acceptable for a CI gate
  that runs O(20) blocks).
* Caching would require a long-lived ``lake env`` subprocess, which
  is fragile to coordinate with a per-block file write/read protocol.
* If startup becomes the bottleneck, the right answer is parallel
  execution under ``pytest-xdist``, not in-process caching.
"""
from __future__ import annotations

import os
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


@dataclass(frozen=True)
class RunResult:
    """Outcome of compiling one extracted block.

    Attributes:
        ok: True iff lake exited 0 AND no ``error:`` line appears in
            stdout/stderr. (Lake sometimes exits 0 on warning-only
            runs; we don't want those to fail.)
        exit_code: lake's exit code.
        stdout: full stdout (combined with stderr — lake interleaves).
        elapsed_ms: wall-clock duration of the lake call.
    """
    ok: bool
    exit_code: int
    stdout: str
    elapsed_ms: int


def run_block(
    body: str,
    *,
    repo_root: Path,
    timeout_s: int = 120,
) -> RunResult:
    """Write ``body`` to a tempfile under ``Pythia/Scratch/MdDoctest/``
    and run ``lake env lean`` on it.

    The scratch path lives inside the existing Pythia.Scratch namespace
    so the file is reachable as a Lean module. We use ``mkstemp`` (not
    ``NamedTemporaryFile``) so the file is fully closed before lake
    opens it — Windows-correct even though we currently target Linux
    runners only.
    """
    import time

    scratch = repo_root / "Pythia" / "Scratch" / "MdDoctest"
    scratch.mkdir(parents=True, exist_ok=True)

    fd, path = tempfile.mkstemp(suffix=".lean", prefix="md_", dir=scratch)
    try:
        with os.fdopen(fd, "w") as fh:
            fh.write(body)
            if not body.endswith("\n"):
                fh.write("\n")

        t0 = time.monotonic()
        try:
            proc = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=repo_root,
                capture_output=True,
                text=True,
                timeout=timeout_s,
            )
        except subprocess.TimeoutExpired as exc:
            elapsed = int((time.monotonic() - t0) * 1000)
            return RunResult(
                ok=False,
                exit_code=-1,
                stdout=f"TIMEOUT after {timeout_s}s\n"
                       f"partial stdout: {(exc.stdout or b'').decode(errors='replace')}\n"
                       f"partial stderr: {(exc.stderr or b'').decode(errors='replace')}",
                elapsed_ms=elapsed,
            )
        elapsed = int((time.monotonic() - t0) * 1000)

        combined = (proc.stdout or "") + (proc.stderr or "")
        # Treat any line starting with "error:" or any non-zero exit as failure.
        has_error_line = any(
            ln.lstrip().startswith("error:") for ln in combined.splitlines()
        )
        ok = proc.returncode == 0 and not has_error_line
        return RunResult(
            ok=ok,
            exit_code=proc.returncode,
            stdout=combined,
            elapsed_ms=elapsed,
        )
    finally:
        try:
            os.unlink(path)
        except FileNotFoundError:
            pass
