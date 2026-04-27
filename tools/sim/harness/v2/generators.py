"""tools.sim.harness.v2.generators — parametric Hypothesis strategies."""
from __future__ import annotations

import math
from hypothesis import strategies as st
from hypothesis.strategies import SearchStrategy


def positive_real() -> SearchStrategy[float]:
    """Strictly-positive real in (0, 1e6]."""
    return st.floats(min_value=1e-9, max_value=1e6, allow_nan=False, allow_infinity=False)


def real_in(low: float, high: float) -> SearchStrategy[float]:
    """Uniform real in [low, high]."""
    return st.floats(min_value=low, max_value=high, allow_nan=False, allow_infinity=False)


def bounded_real(low: float, high: float) -> SearchStrategy[float]:
    """Alias of real_in."""
    return real_in(low, high)


def bounded_iid(low: float, high: float, n: int) -> SearchStrategy[list[float]]:
    """List of n iid draws from Uniform[low, high]."""
    return st.lists(real_in(low, high), min_size=n, max_size=n)


def sub_gaussian_sample(sigma: float, n: int) -> SearchStrategy[list[float]]:
    """n iid draws bounded to ±6σ (N(0,σ²) proxy)."""
    return st.lists(
        st.floats(min_value=-6 * sigma, max_value=6 * sigma, allow_nan=False, allow_infinity=False),
        min_size=n, max_size=n,
    )


def sub_gamma_sample(variance: float, scale: float, n: int) -> SearchStrategy[list[float]]:
    """n iid draws on [0, 6√v + 6s] (sub-Gamma proxy)."""
    bound = math.sqrt(variance) * 6 + scale * 6
    return st.lists(real_in(0.0, bound), min_size=n, max_size=n)


def sample_path_supermartingale(steps: int, drift_max: float) -> SearchStrategy[list[float]]:
    """Downward random walk of length steps+1 (X_0=0 included)."""
    return st.lists(real_in(-drift_max, 0.0), min_size=steps, max_size=steps).map(
        lambda incs: _cumsum([0.0] + incs)
    )


def _cumsum(vals: list[float]) -> list[float]:
    out, acc = [], 0.0
    for v in vals:
        acc += v
        out.append(acc)
    return out


def random_ode_initial(state_dim: int) -> SearchStrategy[list[float]]:
    """Initial condition vector in [-10, 10]^state_dim."""
    return st.lists(real_in(-10.0, 10.0), min_size=state_dim, max_size=state_dim)


def random_density(simplex_dim: int) -> SearchStrategy[list[float]]:
    """Probability vector in the simplex of dimension simplex_dim."""
    return st.lists(
        st.floats(min_value=1e-3, max_value=1.0, allow_nan=False, allow_infinity=False),
        min_size=simplex_dim, max_size=simplex_dim,
    ).map(_normalize)


def _normalize(v: list[float]) -> list[float]:
    s = sum(v)
    return [x / s for x in v] if s > 0 else [1.0 / len(v)] * len(v)


def random_stochastic_matrix(d: int) -> SearchStrategy[list[list[float]]]:
    """Row-stochastic d×d matrix."""
    return st.lists(random_density(d), min_size=d, max_size=d)


def production_inputs(alpha: float, K: float, L: float) -> SearchStrategy[dict]:
    """Cobb-Douglas inputs dict {K, L, alpha}."""
    return st.fixed_dictionaries({
        "K": real_in(1e-2, K),
        "L": real_in(1e-2, L),
        "alpha": st.just(alpha),
    })


__all__ = [
    "bounded_iid", "bounded_real", "positive_real", "production_inputs",
    "random_density", "random_ode_initial", "random_stochastic_matrix",
    "real_in", "sample_path_supermartingale", "sub_gamma_sample", "sub_gaussian_sample",
]
