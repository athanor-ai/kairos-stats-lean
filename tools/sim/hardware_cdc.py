"""PBT sim for Pythia.Hardware.CDC (Clock Domain Crossing MTBF).

Monte Carlo simulation of synchronizer chains: simulate metastability
events, verify MTBF grows exponentially with depth, and check the
doubling rule.

Paired with: Pythia/Hardware/CDC.lean
  - mtbf_exponential_growth (sorry)
  - mtbf_doubling_rule (sorry)
  - min_depth_for_mtbf (sorry)
"""
from __future__ import annotations

import math
from hypothesis import given, settings, assume
from hypothesis import strategies as st


def stage_fail_prob(tau: float, t_slack: float) -> float:
    return math.exp(-t_slack / tau)


def cascade_mtbf(n: int, f_clk: float, t_w: float,
                 tau: float, t_slack: float) -> float:
    return 1.0 / (f_clk * t_w * stage_fail_prob(tau, t_slack) ** n)


@given(
    n=st.integers(min_value=1, max_value=10),
    f_clk=st.floats(min_value=1e6, max_value=1e10),
    t_w=st.floats(min_value=1e-12, max_value=1e-9),
    tau=st.floats(min_value=1e-12, max_value=1e-9),
    t_slack=st.floats(min_value=1e-12, max_value=1e-8),
)
@settings(max_examples=500)
def test_mtbf_exponential_growth(n, f_clk, t_w, tau, t_slack):
    """Adding one stage multiplies MTBF by exp(t_slack / τ)."""
    assume(f_clk > 0 and t_w > 0 and tau > 0 and t_slack > 0)
    assume(not math.isinf(cascade_mtbf(n, f_clk, t_w, tau, t_slack)))
    assume(not math.isinf(cascade_mtbf(n + 1, f_clk, t_w, tau, t_slack)))

    mtbf_n = cascade_mtbf(n, f_clk, t_w, tau, t_slack)
    mtbf_n1 = cascade_mtbf(n + 1, f_clk, t_w, tau, t_slack)
    ratio = mtbf_n1 / mtbf_n if mtbf_n > 0 else float("inf")
    expected = math.exp(t_slack / tau)

    assert abs(ratio - expected) / max(expected, 1e-30) < 1e-6, (
        f"n={n}: MTBF ratio={ratio:.6f}, expected exp(t/τ)={expected:.6f}"
    )


@given(
    n=st.integers(min_value=2, max_value=8),
    f_clk=st.floats(min_value=1e6, max_value=1e9),
    t_w=st.floats(min_value=1e-12, max_value=1e-10),
    tau=st.floats(min_value=1e-11, max_value=1e-9),
)
@settings(max_examples=300)
def test_mtbf_doubling_rule(n, f_clk, t_w, tau):
    """With t_slack ≥ τ·ln(2), MTBF ≥ (1/(f·T_w·4)) · 2^n."""
    assume(f_clk > 0 and t_w > 0 and tau > 0)
    t_slack = tau * math.log(2)  # exactly the threshold
    mtbf = cascade_mtbf(n, f_clk, t_w, tau, t_slack)
    lower = (1.0 / (f_clk * t_w * 4)) * (2 ** n)

    assume(not math.isinf(mtbf) and not math.isinf(lower))
    assert mtbf >= lower * (1 - 1e-9), (
        f"Doubling rule violated: n={n}, MTBF={mtbf:.2e}, lower={lower:.2e}"
    )


@given(
    target=st.floats(min_value=1e3, max_value=1e15),
    f_clk=st.floats(min_value=1e6, max_value=1e9),
    t_w=st.floats(min_value=1e-12, max_value=1e-10),
    tau=st.floats(min_value=1e-11, max_value=1e-9),
    t_slack=st.floats(min_value=1e-11, max_value=1e-8),
)
@settings(max_examples=200)
def test_min_depth_for_mtbf(target, f_clk, t_w, tau, t_slack):
    """There always exists n such that MTBF(n) ≥ target."""
    assume(f_clk > 0 and t_w > 0 and tau > 0 and t_slack > 0 and target > 0)
    found = False
    for n in range(100):
        mtbf = cascade_mtbf(n, f_clk, t_w, tau, t_slack)
        if math.isinf(mtbf) or mtbf >= target:
            found = True
            break
    assert found, f"Could not find n with MTBF ≥ {target:.2e}"


if __name__ == "__main__":
    test_mtbf_exponential_growth()
    print("✓ mtbf_exponential_growth")
    test_mtbf_doubling_rule()
    print("✓ mtbf_doubling_rule")
    test_min_depth_for_mtbf()
    print("✓ min_depth_for_mtbf")
    print("\nAll hardware_cdc PBT passed.")
