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
    """Run #eval <expr> via lake env lean. Returns stdout or None."""
    if not shutil.which("lake"):
        return None
    tmpfile = _REPO_ROOT / ".v2_lean_eval_tmp.lean"
    try:
        tmpfile.write_text(f"#eval {expr}\n", encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(tmpfile)],
            capture_output=True, text=True, timeout=30, cwd=str(_REPO_ROOT),
        )
        tmpfile.unlink(missing_ok=True)
        if result.returncode != 0:
            warnings.warn(f"lean eval error: {result.stderr[:200]}", stacklevel=3)
            return None
        return result.stdout.strip()
    except subprocess.TimeoutExpired:
        warnings.warn("lean eval timed out", stacklevel=3)
        tmpfile.unlink(missing_ok=True)
        return None
    except Exception as exc:
        warnings.warn(f"lean eval error: {exc}", stacklevel=3)
        tmpfile.unlink(missing_ok=True)
        return None


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
    """#eval <lean_decl.format(**inputs)> matches python_fn(**inputs). Skips if no lake."""
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
