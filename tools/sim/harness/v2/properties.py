"""tools.sim.harness.v2.properties — composable property checks."""
from __future__ import annotations

import math
from typing import Any, Callable, Optional, Sequence

Property = Callable[..., bool]


def tail_bound(
    samples: Sequence[float],
    threshold: float,
    claimed_bound: float,
    *,
    atol: float = 0.0,
) -> bool:
    """Empirical P(X > threshold) <= claimed_bound + atol."""
    if not samples:
        return True
    return sum(1 for x in samples if x > threshold) / len(samples) <= claimed_bound + atol


def identity(
    lhs_fn: Callable[..., float],
    rhs_fn: Callable[..., float],
    inputs: dict[str, Any],
    *,
    tolerance: float = 1e-9,
    symbolic: bool = False,
) -> bool:
    """lhs_fn(**inputs) == rhs_fn(**inputs) within tolerance (symbolic ignored)."""
    lhs, rhs = lhs_fn(**inputs), rhs_fn(**inputs)
    return math.isclose(lhs, rhs, rel_tol=tolerance, abs_tol=tolerance)


def monotone(
    fn: Callable[..., float],
    base_inputs: dict[str, Any],
    arg: str,
    *,
    n_steps: int = 10,
    lo: Optional[float] = None,
    hi: Optional[float] = None,
) -> bool:
    """fn is non-decreasing in arg over [lo, hi]."""
    base_val = base_inputs[arg]
    _lo = lo if lo is not None else base_val * 0.1
    _hi = hi if hi is not None else base_val * 10.0
    if _lo >= _hi:
        _lo, _hi = min(_lo, _hi) - 1.0, max(_lo, _hi) + 1.0
    step = (_hi - _lo) / max(1, n_steps - 1)
    prev: Optional[float] = None
    for i in range(n_steps):
        cur = fn(**{**base_inputs, arg: _lo + i * step})
        if prev is not None and cur < prev - 1e-12:
            return False
        prev = cur
    return True


def convergence(
    sequence_fn: Callable[[int], float],
    target: float,
    n_steps: int,
    *,
    rate: Optional[float] = None,
) -> bool:
    """sequence_fn(n_steps) is close to target; optionally checks convergence rate."""
    final = sequence_fn(n_steps)
    if not math.isfinite(final) or abs(final - target) >= 1e-4 * (1 + abs(target)):
        return False
    if rate is not None and n_steps >= 2:
        v1 = abs(sequence_fn(1) - target)
        vn = abs(final - target)
        if v1 > 0 and vn > v1 / (n_steps ** rate) * 10:
            return False
    return True


def martingale_property(
    path: Sequence[float],
    filtration_fn: Optional[Callable[[Sequence[float], int], float]] = None,
    *,
    tolerance: float = 1e-6,
) -> bool:
    """E[X_{t+1} | F_t] = X_t with tolerance (filtration_fn=None uses X_t)."""
    for t in range(len(path) - 1):
        expected = filtration_fn(path, t) if filtration_fn else path[t]
        if abs(expected - path[t + 1]) > tolerance * (1 + abs(path[t])):
            return False
    return True


def ergodic_match(
    time_average: float,
    space_average: float,
    *,
    tolerance: float = 1e-3,
) -> bool:
    """|time_average - space_average| <= tolerance."""
    return abs(time_average - space_average) <= tolerance


__all__ = [
    "Property", "convergence", "ergodic_match", "identity",
    "martingale_property", "monotone", "tail_bound",
]
