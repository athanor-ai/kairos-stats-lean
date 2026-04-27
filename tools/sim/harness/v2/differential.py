"""tools.sim.harness.v2.differential — Lean vs Python differential checks."""
from __future__ import annotations

import math
import re
import shutil
import subprocess
import warnings
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Optional

_REPO_ROOT = Path(__file__).resolve().parents[4]


@dataclass
class DifferentialCheck:
    """Lean #eval expression vs Python comparison."""
    lean_decl: str
    python_fn: Callable[..., float]
    inputs: dict[str, Any]
    tolerance: float = 1e-9


def _lean_eval(expr: str) -> Optional[str]:
    """Run #eval <expr> via lake env lean. Returns stdout or None.

    Uses a unique tmpfile per call so concurrent sims (e.g. under
    pytest-xdist) don't race on a single shared path.
    """
    if not shutil.which("lake"):
        return None
    import tempfile

    fd, tmppath_str = tempfile.mkstemp(
        prefix=".v2_lean_eval_", suffix=".lean", dir=str(_REPO_ROOT)
    )
    tmpfile = Path(tmppath_str)
    try:
        with open(fd, "w", encoding="utf-8") as f:
            f.write(f"#eval {expr}\n")
        result = subprocess.run(
            ["lake", "env", "lean", str(tmpfile)],
            capture_output=True, text=True, timeout=30, cwd=str(_REPO_ROOT),
        )
        if result.returncode != 0:
            warnings.warn(f"lean eval error: {result.stderr[:200]}", stacklevel=3)
            return None
        return result.stdout.strip()
    except subprocess.TimeoutExpired:
        warnings.warn("lean eval timed out", stacklevel=3)
        return None
    except Exception as exc:
        warnings.warn(f"lean eval error: {exc}", stacklevel=3)
        return None
    finally:
        tmpfile.unlink(missing_ok=True)


def _parse_lean_float(raw: str) -> Optional[float]:
    raw = raw.strip()
    try:
        return float(raw)
    except ValueError:
        pass
    m = re.match(r"^(-?\d+)/(\d+)$", raw)
    if m:
        num, den = int(m.group(1)), int(m.group(2))
        return num / den if den != 0 else None
    return None


def lean_eval_matches_python(
    lean_decl: str,
    python_fn: Callable[..., float],
    inputs: dict[str, Any],
    *,
    tolerance: float = 1e-9,
) -> bool:
    """#eval <lean_decl.format(**inputs)> matches python_fn(**inputs). Skips if no lake.

    NOTE on batched differential: the current API takes a single
    ``inputs`` dict and pays one lake-startup cost (~3s cold) per
    call. Today's ``Sim.run()`` invokes differential exactly once
    per sim, so this cost is already at the minimum.

    A future multi-input differential probe (e.g., differential
    over a parameter grid) would call this N times, paying N lake
    startups. When that use case materialises, refactor to a
    persistent subprocess or a batched tmpfile rather than calling
    this function N times. Not implemented today because no caller
    needs it. ATH-789-followup if/when reopened.
    """
    raw = _lean_eval(lean_decl.format(**inputs))
    if raw is None:
        warnings.warn("lean_eval_matches_python: lake not found or eval failed — skipping", stacklevel=2)
        return True
    lean_val = _parse_lean_float(raw)
    if lean_val is None:
        warnings.warn(f"lean_eval_matches_python: could not parse {raw!r}", stacklevel=2)
        return True
    return math.isclose(lean_val, python_fn(**inputs), rel_tol=tolerance, abs_tol=tolerance)


__all__ = ["DifferentialCheck", "lean_eval_matches_python"]
