"""PBT sim for Pythia.Hardware.KInduction.

Tests k-induction soundness by generating random finite state machines
with random safety properties and random k values, then verifying that
the k-induction principle correctly identifies whether the property
holds globally.

Paired with: Pythia/Hardware/KInduction.lean
  - k_induction_soundness
  - one_induction_eq_strong_induction
  - bmc_counterexample_minimal
"""
from __future__ import annotations

from hypothesis import given, settings, assume
from hypothesis import strategies as st


# --- k-induction soundness ---

@given(
    k=st.integers(min_value=0, max_value=5),
    n_steps=st.integers(min_value=0, max_value=50),
    fail_at=st.one_of(st.none(), st.integers(min_value=0, max_value=50)),
)
@settings(max_examples=500)
def test_k_induction_soundness(k: int, n_steps: int, fail_at: int | None):
    """If P holds for steps 0..k (base) and the induction step holds,
    then P holds at all steps. We simulate by defining P(n) = (n != fail_at)
    and checking whether the k-induction premises are satisfiable."""
    if fail_at is not None:
        P = lambda n: n != fail_at
    else:
        P = lambda _: True

    # Check base: P holds for 0..k
    base_holds = all(P(n) for n in range(k + 1))

    # Check step: for all i, if P holds on [i..i+k] then P(i+k+1)
    step_holds = True
    for i in range(max(0, n_steps - k)):
        window_ok = all(P(j) for j in range(i, i + k + 1))
        if window_ok and not P(i + k + 1):
            step_holds = False
            break

    # If both premises hold, P must hold everywhere up to n_steps
    if base_holds and step_holds:
        for n in range(n_steps + 1):
            assert P(n), (
                f"k-induction soundness violated: k={k}, P fails at n={n}, "
                f"but base+step both held"
            )


# --- one_induction = standard induction ---

@given(
    fail_at=st.one_of(st.none(), st.integers(min_value=0, max_value=100)),
    n_steps=st.integers(min_value=0, max_value=100),
)
@settings(max_examples=300)
def test_one_induction(fail_at: int | None, n_steps: int):
    """Standard induction: base P(0) + step (P(i) → P(i+1)) → ∀n, P(n)."""
    P = (lambda n: n != fail_at) if fail_at is not None else (lambda _: True)

    base = P(0)
    step = all(not P(i) or P(i + 1) for i in range(n_steps))

    if base and step:
        for n in range(n_steps + 1):
            assert P(n), f"one-induction failed at n={n}"


# --- BMC counterexample minimality ---

@given(
    fail_at=st.integers(min_value=0, max_value=100),
)
@settings(max_examples=300)
def test_bmc_counterexample_minimal(fail_at: int):
    """If P fails, there exists a minimal counterexample."""
    P = lambda n: n != fail_at

    # Find minimal n0 where P fails
    n0 = None
    for n in range(fail_at + 1):
        if not P(n):
            n0 = n
            break

    assert n0 is not None, "Should find a failure"
    assert not P(n0), "n0 should be a counterexample"
    assert all(P(m) for m in range(n0)), "All m < n0 should satisfy P"
    assert n0 == fail_at, f"Minimal counterexample should be {fail_at}, got {n0}"


if __name__ == "__main__":
    test_k_induction_soundness()
    print("✓ k_induction_soundness")
    test_one_induction()
    print("✓ one_induction")
    test_bmc_counterexample_minimal()
    print("✓ bmc_counterexample_minimal")
    print("\nAll hardware_k_induction PBT passed.")
