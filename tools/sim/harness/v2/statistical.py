"""tools.sim.harness.v2.statistical — CI helpers for pass/fail counts."""
from __future__ import annotations

from scipy.stats import beta as beta_dist
from scipy.stats import norm as norm_dist


def wilson_ci(successes: int, n: int, *, level: float = 0.99) -> tuple[float, float]:
    """Wilson score confidence interval for a proportion."""
    if n == 0:
        return 0.0, 1.0
    alpha = 1.0 - level
    z = norm_dist.ppf(1.0 - alpha / 2.0)
    p_hat = successes / n
    denom = 1.0 + z ** 2 / n
    centre = (p_hat + z ** 2 / (2 * n)) / denom
    margin = (z / denom) * (p_hat * (1 - p_hat) / n + z ** 2 / (4 * n ** 2)) ** 0.5
    return max(0.0, centre - margin), min(1.0, centre + margin)


def clopper_pearson_ci(successes: int, n: int, *, level: float = 0.99) -> tuple[float, float]:
    """Exact Clopper-Pearson binomial confidence interval."""
    if n == 0:
        return 0.0, 1.0
    alpha = 1.0 - level
    lo = beta_dist.ppf(alpha / 2.0, successes, n - successes + 1) if successes > 0 else 0.0
    hi = beta_dist.ppf(1.0 - alpha / 2.0, successes + 1, n - successes) if successes < n else 1.0
    return lo, hi


def binomial_ci_check(
    violations: int,
    n: int,
    claimed_prob: float,
    *,
    ci_level: float = 0.99,
    method: str = "clopper_pearson",
) -> bool:
    """Upper CI bound on violation rate <= claimed_prob."""
    fn = wilson_ci if method == "wilson" else clopper_pearson_ci
    _lo, upper = fn(violations, n, level=ci_level)
    return bool(upper <= claimed_prob)


__all__ = ["binomial_ci_check", "clopper_pearson_ci", "wilson_ci"]
